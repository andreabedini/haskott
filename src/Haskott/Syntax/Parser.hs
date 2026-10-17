{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE OverloadedStrings #-}

-- | The stage-one parser: Ott source text to a lossless green tree.
--
-- This module implements @GRAMMAR.md@. The lexer modes of §2 are the
-- @lex*@ functions, the syntactic grammar of §3 the @p*@ functions, and the
-- rule bodies of §4 'defnBody' and 'funBody'. The tree keeps every character
-- of the input: 'parseDocument' followed by 'Graft.Green.renderNode' is the
-- identity on accepted inputs.
--
-- Trivia placement follows §7: a node spans from its first to its last
-- syntax token, an item also owns the whitespace directly in front of it and
-- the trivia to the end of its last line, and comment lines after an item
-- indented past the item's column stay with it (Rule 2). The item loops
-- ('itemLoop', 'defnBody', 'funBody') implement this by handing trailing
-- trivia back to the enclosing node and re-attaching what the rules give to
-- the item ('attach').
module Haskott.Syntax.Parser
  ( ParseError (..)
  , parseDocument
  , parseErrorPosition
  , metaKeywords
  ) where

import Control.Monad (ap, liftM)
import Data.Char (isAsciiLower, isAsciiUpper, isDigit)
import Data.List (find)
import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Text.Foreign as TF
import Graft.Green
  ( GreenElement (..)
  , GreenNode
  , elementKind
  , elementTextLength
  , greenNode
  , greenToken
  , nodeChildren
  , nodeKind
  )
import Haskott.Syntax.Kind

type Elem = GreenElement Kind

-- | Where and why a parse failed. The offset counts UTF-8 bytes from the
-- start of the input; 'parseErrorPosition' turns it into a line and column.
data ParseError = ParseError
  { parseErrorOffset :: !Int
  , parseErrorMessage :: !Text
  }
  deriving (Eq, Show)

-- | One-based line and column (in characters) of an error in its source.
parseErrorPosition :: Text -> ParseError -> (Int, Int)
parseErrorPosition src (ParseError off _) =
  let pre = TF.takeWord8 (fromIntegral (min off (byteLen src))) src
      lineText = T.takeWhileEnd (\c -> c /= '\n' && c /= '\r') pre
      before = T.dropWhileEnd (\c -> c /= '\n' && c /= '\r') pre
      nls = T.count "\n" before + T.count "\r" before - T.count "\r\n" before
   in (nls + 1, T.length lineText + 1)

-- | Parse a whole Ott source file into a 'Document' node.
parseDocument :: Text -> Either ParseError (GreenNode Kind)
parseDocument src = fst <$> unP pDocument (S src 0 0)

------------------------------------------------------------------------
-- The parser monad

data S = S
  { sRest :: !Text
  , sOff :: !Int
  -- ^ byte offset of 'sRest' in the input
  , sLineStart :: !Int
  -- ^ byte offset of the start of the current line
  }

newtype P a = P {unP :: S -> Either ParseError (a, S)}

instance Functor P where
  fmap = liftM

instance Applicative P where
  pure a = P $ \s -> Right (a, s)
  (<*>) = ap

instance Monad P where
  P g >>= k = P $ \s -> case g s of
    Left e -> Left e
    Right (a, s') -> unP (k a) s'

getS :: P S
getS = P $ \s -> Right (s, s)

putS :: S -> P ()
putS s = P $ \_ -> Right ((), s)

failHere :: Text -> P a
failHere msg = P $ \s -> Left (ParseError (sOff s) msg)

-- | Run a parser and forget what it consumed.
peekP :: P a -> P a
peekP (P g) = P $ \s -> case g s of
  Left e -> Left e
  Right (a, _) -> Right (a, s)

rest :: P Text
rest = sRest <$> getS

-- | Consume a prefix of the remaining input, which the caller has already
-- checked is a prefix, keeping the line start up to date.
take' :: Text -> P ()
take' t = do
  s <- getS
  let n = byteLen t
      before = T.dropWhileEnd (\c -> c /= '\n' && c /= '\r') t
      ls
        | T.null before = sLineStart s
        | otherwise = sOff s + byteLen before
  putS s {sRest = TF.dropWord8 (fromIntegral n) (sRest s), sOff = sOff s + n, sLineStart = ls}

-- | Consume text as a token.
tokenOf :: Kind -> Text -> P Elem
tokenOf k t = do
  take' t
  pure (Token (greenToken k t))

node :: Kind -> [Elem] -> Elem
node k = Node . greenNode k

-- | A node that spans from its first syntax token: leading trivia stays
-- outside, in front of it.
tight :: Kind -> [Elem] -> [Elem]
tight k es =
  let (lead, body) = span (isTrivia . elementKind) es
   in lead ++ [node k body]

-- | Run a parser on the current line only, up to but excluding its
-- terminator, as Ott does when it re-lexes the annotation of a rule line.
-- The parser must consume the whole line.
withinLine :: P a -> P a
withinLine p = do
  s <- getS
  let line = T.takeWhile (\c -> c /= '\n' && c /= '\r') (sRest s)
  case unP p s {sRest = line} of
    Left e -> P (const (Left e))
    Right (a, s') -> do
      let consumed = sOff s' - sOff s
      putS s' {sRest = TF.dropWord8 (fromIntegral consumed) (sRest s)}
      pure a

------------------------------------------------------------------------
-- Character classes (GRAMMAR.md §2.2)

isNnws :: Char -> Bool
isNnws c = c == ' ' || c == '\t' || c == '\f'

isNl :: Char -> Bool
isNl c = c == '\n' || c == '\r'

isWs :: Char -> Bool
isWs c = isNnws c || isNl c

isIdentChar :: Char -> Bool
isIdentChar c = isAsciiUpper c || isAsciiLower c || isDigit c || c == '_' || c == '\''

------------------------------------------------------------------------
-- Trivia (GRAMMAR.md §2.4, §2.8, §2.10)

data TriviaMode = TriviaMode
  { tmLineComments :: !Bool
  , tmBlockComments :: !Bool
  , tmCommentNeedsNewline :: !Bool
  }

-- | Whitespace and comments as @metalang@ discards them. A @%@ comment must
-- end with a newline.
metaTrivia :: TriviaMode
metaTrivia = TriviaMode True True True

-- | As @bindspec@ discards them. A @%@ comment may end the file.
bindTrivia :: TriviaMode
bindTrivia = TriviaMode True True False

-- | Whitespace only, as @elements@ and @comp_bound@ discard it.
wsTrivia :: TriviaMode
wsTrivia = TriviaMode False False False

trivia :: TriviaMode -> P [Elem]
trivia tm = go []
  where
    go acc = do
      r <- rest
      case T.uncons r of
        Nothing -> pure (reverse acc)
        Just (c, _)
          | isNnws c -> tokenOf Space (T.takeWhile isNnws r) >>= \e -> go (e : acc)
          | isNl c -> newlineToken r >>= \e -> go (e : acc)
          | c == '%' && tmLineComments tm -> do
              let (cm, after) = T.break isNl r
              if T.null after && tmCommentNeedsNewline tm
                then failHere "a % comment must end with a newline here (Ott lexing error)"
                else tokenOf LineComment cm >>= \e -> go (e : acc)
          | tmBlockComments tm && ">>" `T.isPrefixOf` r -> blockComment r >>= \e -> go (e : acc)
          | otherwise -> pure (reverse acc)

newlineToken :: Text -> P Elem
newlineToken r
  | "\r\n" `T.isPrefixOf` r = tokenOf Newline "\r\n"
  | otherwise = tokenOf Newline (T.take 1 r)

-- | A @>>@ ... @<<@ comment, nesting included, as one token.
blockComment :: Text -> P Elem
blockComment r = case scan (T.drop 2 r) (1 :: Int) 2 of
  Nothing -> failHere "unclosed >> comment (Ott lexing error)"
  Just n -> tokenOf BlockComment (T.take n r)
  where
    scan t !lvl !n
      | T.null t = Nothing
      | "%" `T.isPrefixOf` t =
          let (cm, after) = T.break isNl t
           in scan after lvl (n + T.length cm)
      | "<<" `T.isPrefixOf` t =
          if lvl == 1 then Just (n + 2) else scan (T.drop 2 t) (lvl - 1) (n + 2)
      | ">>" `T.isPrefixOf` t = scan (T.drop 2 t) (lvl + 1) (n + 2)
      | otherwise = scan (T.drop 1 t) lvl (n + 1)

------------------------------------------------------------------------
-- Mode metalang (GRAMMAR.md §2.4)

data MTok
  = MEof
  | MKw !Text
  | MIdent
  | MSym !Text
  deriving (Eq, Show)

metaKeywords :: [Text]
metaKeywords =
  [ "embed", "homs", "metavar", "indexvar", "grammar", "subrules", "contextrules"
  , "substitutions", "single", "multiple", "freevars", "parsing", "begincoqsection"
  , "endcoqsection", "coqvariable", "left", "right", "non", "defns", "funs", "defn"
  , "fun", "by"
  ]

-- | Keywords that start an item (§3.1), and therefore end whatever came
-- before.
itemKeywords :: [Text]
itemKeywords =
  [ "metavar", "indexvar", "grammar", "subrules", "contextrules", "substitutions"
  , "freevars", "defns", "funs", "embed", "parsing", "homs", "begincoqsection"
  , "endcoqsection", "coqvariable"
  ]

-- | Longest first, so that the first prefix match is the longest match.
metaSymbols :: [(Text, Kind)]
metaSymbols =
  [ ("::=", ColonColonEq), ("<::", LtColonColon), ("_::", UnderscoreColonColon)
  , ("{{*", HomOpen), ("*}}", HomClose)
  , ("::", ColonColon), ("{{", HomOpen), ("}}", HomClose), ("<=", LtEq), ("(+", BindOpen)
  , (",", Comma), ("|", Bar)
  ]

-- | The next @metalang@ token after trivia has been taken. The identifier
-- rule and the symbol rules compete by longest match; a run of identifier
-- characters that spells a keyword is the keyword.
lexMeta :: P (MTok, [Elem])
lexMeta = do
  r <- rest
  if T.null r
    then pure (MEof, [])
    else do
      let identRun = T.takeWhile isIdentChar r
          il = T.length identRun
          sym = find (\(s, _) -> s `T.isPrefixOf` r) metaSymbols
      case sym of
        Just (s, k) | il <= T.length s -> do
          e <- tokenOf k s
          pure (MSym s, [e])
        _
          | il > 0 && identRun `elem` metaKeywords -> do
              e <- tokenOf Keyword identRun
              pure (MKw identRun, [e])
          | il > 0 -> do
              e <- tokenOf Ident identRun
              pure (MIdent, [e])
          | otherwise -> failHere ("lexing error: unexpected " <> T.take 1 r)

-- | Look at the next @metalang@ token, past trivia, without consuming.
mPeek :: P MTok
mPeek = peekP (trivia metaTrivia >> (fst <$> lexMeta))

-- | Consume trivia and the next token if it satisfies the test; otherwise
-- fail at the token with the message.
mExpect :: (MTok -> Bool) -> Text -> P [Elem]
mExpect ok what = do
  tv <- trivia metaTrivia
  t <- peekP (fst <$> lexMeta)
  if ok t
    then do
      (_, es) <- lexMeta
      pure (tv ++ es)
    else failHere ("expected " <> what)

mSym :: Text -> P [Elem]
mSym s = mExpect (== MSym s) s

mKw :: Text -> P [Elem]
mKw k = mExpect (== MKw k) k

mIdent :: Text -> P [Elem]
mIdent what = mExpect (== MIdent) what

------------------------------------------------------------------------
-- Items and trivia placement (GRAMMAR.md §7)

-- | A step of an item loop: given the item's column (when it starts its
-- line) and the whitespace in front of it, either parse one item, returning
-- its node and the trivia it consumed past its end, or return 'Nothing'
-- without consuming anything.
type Step = Maybe Int -> [Elem] -> P (Maybe (GreenNode Kind, [Elem]))

-- | Parse items separated by trivia. Returns the children of the enclosing
-- node and the trailing trivia that belongs to the enclosing node's parent.
-- The initial pending trivia is what the caller consumed before the first
-- item.
itemLoop :: TriviaMode -> [Elem] -> Step -> P ([Elem], [Elem])
itemLoop tm pending0 step = go Nothing [] pending0
  where
    go prev acc pending = do
      tv <- trivia tm
      let triv0 = pending ++ tv
          (acc', triv) = case prev of
            Nothing -> (acc, triv0)
            Just (n, col) ->
              let (n', remaining) = attach col n triv0
               in (acc ++ [Node n'], remaining)
          (before, indent) = splitIndent triv
      col <- itemColumn indent
      r <- step col indent
      case r of
        Nothing -> pure (acc', triv)
        Just (n, leftover) -> do
          let (n', trailing) = peel n
          go (Just (n', col)) (acc' ++ before) (trailing ++ leftover)

-- | The whitespace directly in front of an item is the item's.
splitIndent :: [Elem] -> ([Elem], [Elem])
splitIndent es = case reverse es of
  (e : rs) | elementKind e == Space -> (reverse rs, [e])
  _ -> (es, [])

-- | The column of an item that starts its line, measured as the width of
-- its indentation, or 'Nothing' for an item that follows other text.
itemColumn :: [Elem] -> P (Maybe Int)
itemColumn indent = do
  s <- getS
  let w = sum (map elementTextLength indent)
  pure (if sOff s - w == sLineStart s then Just w else Nothing)

-- | Take a node's trailing trivia children off it.
peel :: GreenNode Kind -> (GreenNode Kind, [Elem])
peel n =
  let (trailingRev, bodyRev) = span (isTrivia . elementKind) (reverse (nodeChildren n))
   in (greenNode (nodeKind n) (reverse bodyRev), reverse trailingRev)

-- | Give an item the trivia that is its own: everything to the end of its
-- last line, and (Rule 2) the comment lines after it that are indented past
-- its column, together with the blank lines between them. The rest goes to
-- the parent.
attach :: Maybe Int -> GreenNode Kind -> [Elem] -> (GreenNode Kind, [Elem])
attach mcol n triv =
  let (sameLine, afterNl) = span ((/= Newline) . elementKind) triv
      claimed = maybe [] (`rule2` afterNl) mcol
      keep = sameLine ++ claimed
   in (greenNode (nodeKind n) (nodeChildren n ++ keep), drop (length keep) triv)

-- | The longest prefix of lines consisting of comment lines indented past
-- the column and blank lines, ending with a comment line. Each line here
-- starts with its newline token.
rule2 :: Int -> [Elem] -> [Elem]
rule2 col es = concat (take best ls)
  where
    ls = linesOf es
    best = pick 0 0 ls
    pick _ acc [] = acc
    pick i acc (l : more) = case classify l of
      Just True -> pick (i + 1) (i + 1) more
      Just False -> pick (i + 1) acc more
      Nothing -> acc
    -- Just True: a comment line indented past the column; Just False: a
    -- blank line; Nothing: anything else.
    classify l = case map elementKind (drop 1 l) of
      [] -> Just False
      [Space] -> Just False
      [LineComment] -> Nothing
      [Space, LineComment] ->
        if elementTextLength (l !! 1) > col then Just True else Nothing
      _ -> Nothing
    linesOf [] = []
    linesOf (e : more) =
      let (l, after) = span ((/= Newline) . elementKind) more
       in (e : l) : linesOf after

-- | Separate the trailing trivia from a list of elements.
splitTrailing :: [Elem] -> ([Elem], [Elem])
splitTrailing es =
  let (tRev, bRev) = span (isTrivia . elementKind) (reverse es)
   in (reverse bRev, reverse tRev)

------------------------------------------------------------------------
-- Files and items (GRAMMAR.md §3.1)

pDocument :: P (GreenNode Kind)
pDocument = do
  (children, leftover) <- itemLoop metaTrivia [] step
  pure (greenNode Document (children ++ leftover))
  where
    step _ indent = do
      t <- mPeek
      case t of
        MEof -> pure Nothing
        MKw k | k `elem` itemKeywords -> Just <$> pItem k indent
        _ -> failHere "expected a section keyword (metavar, grammar, defns, ...)"

pItem :: Text -> [Elem] -> P (GreenNode Kind, [Elem])
pItem k indent = case k of
  "metavar" -> simple MetavarDecl pMetavar
  "indexvar" -> simple MetavarDecl pMetavar
  "grammar" -> section GrammarSection ruleStep
  "subrules" -> section SubrulesSection subruleStep
  "contextrules" -> section ContextrulesSection contextruleStep
  "substitutions" -> section SubstitutionsSection substitutionStep
  "freevars" -> section FreevarsSection freevarStep
  "embed" -> section EmbedSection embedStep
  "parsing" -> section ParsingSection parsingStep
  "homs" -> homsSection
  "defns" -> pDefns indent
  "funs" -> pFuns indent
  "begincoqsection" -> simple CoqSection (kwIdent "begincoqsection")
  "endcoqsection" -> simple CoqSection (kwIdent "endcoqsection")
  "coqvariable" -> simple CoqVariable (kwIdent "coqvariable")
  _ -> failHere "internal error: not an item keyword"
  where
    simple kind body = do
      es <- body
      pure (greenNode kind (indent ++ es), [])
    kwIdent w = (++) <$> mKw w <*> mIdent "a name"
    section kind step = do
      kw <- mKw k
      (children, leftover) <- itemLoop metaTrivia [] step
      pure (greenNode kind (indent ++ kw ++ children), leftover)
    homsSection = do
      header <- (++) <$> mKw "homs" <*> mIdent "a production-name prefix"
      let (header', pending) = splitTrailing header
      (children, leftover) <- itemLoop metaTrivia pending homsItemStep
      pure (greenNode HomsSection (indent ++ header' ++ children), leftover)

-- | End of a section: an item keyword or the end of the file.
endsSection :: MTok -> Bool
endsSection t = case t of
  MEof -> True
  MKw k -> k `elem` itemKeywords
  _ -> False

------------------------------------------------------------------------
-- Metavariables, names and homs (GRAMMAR.md §3.2, §3.6)

pMetavar :: P [Elem]
pMetavar = do
  kw <- mExpect isMv "metavar or indexvar"
  names <- pNames
  cce <- mSym "::="
  homs <- pHoms
  pure (kw ++ names ++ cce ++ homs)
  where
    isMv t = t == MKw "metavar" || t == MKw "indexvar"

-- | @ident hom* (, ident hom*)*@, each name as a 'Name' node.
pNames :: P [Elem]
pNames = do
  n <- pName
  t <- mPeek
  case t of
    MSym "," -> do
      c <- mSym ","
      more <- pNames
      pure (n ++ c ++ more)
    _ -> pure n
  where
    pName = do
      i <- mIdent "a name"
      homs <- pHoms
      let (homs', trailing) = splitTrailing homs
      pure (tight Name (i ++ homs') ++ trailing)

-- | Zero or more homs. Trailing trivia is returned too, so the caller must
-- place it ('splitTrailing').
pHoms :: P [Elem]
pHoms = do
  tv <- trivia metaTrivia
  t <- peekP (fst <$> lexMeta)
  case t of
    MSym "{{" -> more tv False
    MSym "{{*" -> more tv True
    _ -> pure tv
  where
    more tv star = do
      (_, open) <- lexMeta
      body <- homBody star HomBody
      next <- pHoms
      pure (tv ++ [node Hom (open ++ body)] ++ next)

-- | What a @{{ }}@ body may contain: a hom (§3.6), an embed (§3.7), or the
-- rest of a comment block after @{{com@ (§4).
data HomFlavour = HomBody | EmbedBody | DefnComBody
  deriving (Eq)

-- | From after the opening braces to the closing braces inclusive.
homBody :: Bool -> HomFlavour -> P [Elem]
homBody star flavour = do
  name <- if flavour == DefnComBody then pure [] else homName
  els <- elements
  pure (name ++ els)
  where
    -- hom_name ::= BLANKS? string BLANKS
    homName = do
      (t1, e1) <- lexHom star
      (t2, e2) <- case t1 of
        HBlank -> lexHom star
        _ -> pure (t1, e1)
      let e1' = if t1 == HBlank then e1 else []
      case t2 of
        HText -> do
          (t3, e3) <- lexHom star
          case t3 of
            HBlank -> pure (e1' ++ e2 ++ e3)
            _ -> failHere "a hom name must be followed by whitespace"
        _ -> failHere "expected a hom name"
    elements = do
      (t, e) <- lexHom star
      case t of
        HClose -> pure e
        HEof -> failHere "unclosed {{ (expected }})"
        HOpen -> failHere "{{ inside a hom"
        HCompLeft -> failHere "</ outside [[ ]] in a hom"
        HRefClose -> failHere "]] without [["
        HRefOpen -> do
          inner <- homRef
          more <- elements
          pure ((node HomRef (e ++ inner)) : more)
        _ -> (e ++) <$> elements
    -- From after [[ to ]] inclusive.
    homRef = do
      (t, e) <- lexHom star
      case t of
        HCompLeft
          | flavour == HomBody -> do
              comp <- homComp
              (e ++) <$> (comp ++) <$> refEnd
        _ -> refInner False (t, e)
    refInner seenDots (t, e) = case t of
      HRefClose -> pure e
      HText -> (e ++) <$> (lexHom star >>= refInner seenDots)
      HBlank -> (e ++) <$> (lexHom star >>= refInner seenDots)
      HDots
        | flavour == HomBody && not seenDots -> (e ++) <$> (lexHom star >>= refInner True)
      HEof -> failHere "unclosed [[ in a hom"
      _ -> failHere "unexpected token inside [[ ]]"
    -- blanks then ]]
    refEnd = do
      (t, e) <- lexHom star
      case t of
        HBlank -> (e ++) <$> refEnd
        HRefClose -> pure e
        _ -> failHere "expected ]] after a comprehension"
    -- comp_bound mode: strings* // comp_bound />
    homComp = do
      items <- compStrings
      mid <- cExpect (== CMiddle) "//"
      bound <- pCompBoundWith lexCompBound
      close <- cExpect (== CClose) "/>"
      pure (items ++ mid ++ bound ++ close)
    compStrings = do
      tv <- trivia wsTrivia
      t <- peekP (fst <$> lexCompBound)
      case t of
        CString -> do
          (_, e) <- lexCompBound
          ((tv ++ e) ++) <$> compStrings
        _ -> pure tv

data HTok = HEof | HBlank | HRefOpen | HRefClose | HOpen | HClose | HText | HDots | HCompLeft
  deriving (Eq, Show)

-- | The next token of the @hom@ (or, with the flag, @hom_star@) mode, by
-- longest match with Ott's rule order on ties (GRAMMAR.md §2.6).
lexHom :: Bool -> P (HTok, [Elem])
lexHom star = do
  r <- rest
  case T.uncons r of
    Nothing -> pure (HEof, [])
    Just (c, _)
      | isNl c -> blank <$> newlineToken r
      | otherwise -> do
          let nn = T.length (T.takeWhile isNnws r)
              spaces = T.length (T.takeWhile (== ' ') r)
              compLen
                | "</" `T.isPrefixOf` T.drop spaces r = spaces + 2
                | otherwise = 0
              runLen = T.length (T.takeWhile runChar r)
          if nn > 0
            then
              if compLen > nn
                then do
                  sp <- if spaces > 0 then (: []) <$> tokenOf Space (T.take spaces r) else pure []
                  e <- tokenOf CompOpen "</"
                  pure (HCompLeft, sp ++ [e])
                else blank <$> tokenOf Space (T.take nn r)
            else
              if
                | star && "*}}" `T.isPrefixOf` r -> one HClose HomClose "*}}"
                | not star && "}}" `T.isPrefixOf` r -> one HClose HomClose "}}"
                | not star && "{{" `T.isPrefixOf` r -> one HOpen HomOpen "{{"
                | "[[" `T.isPrefixOf` r -> one HRefOpen RefOpen "[["
                | "]]" `T.isPrefixOf` r -> one HRefClose RefClose "]]"
                | "...." `T.isPrefixOf` r -> one HDots Dots "...."
                | "..." `T.isPrefixOf` r -> one HDots Dots "..."
                | ".." `T.isPrefixOf` r -> one HDots Dots ".."
                | compLen == 2 && compLen >= runLen -> one HCompLeft CompOpen "</"
                | runLen > 0 -> one HText HomText (T.take runLen r)
                | otherwise -> one HText HomText (T.take 1 r)
  where
    blank e = (HBlank, [e])
    one t k s = do
      e <- tokenOf k s
      pure (t, [e])
    runChar ch
      | isWs ch = False
      | star = ch `notElem` ("[]*." :: String)
      | otherwise = ch `notElem` ("[]{}." :: String)

data CTok = CEof | CDots | COpen | CMiddle | CClose | CIn | CString
  deriving (Eq, Show)

-- | The next token of the @comp_bound@ mode (GRAMMAR.md §2.7): a run of
-- non-whitespace, classified exactly.
lexCompBound :: P (CTok, [Elem])
lexCompBound = do
  r <- rest
  let run = T.takeWhile (not . isWs) r
  if T.null run
    then pure (CEof, [])
    else do
      let (t, k) = case run of
            ".." -> (CDots, Dots)
            "..." -> (CDots, Dots)
            "...." -> (CDots, Dots)
            "</" -> (COpen, CompOpen)
            "//" -> (CMiddle, CompMiddle)
            "/>" -> (CClose, CompClose)
            "IN" -> (CIn, CompIn)
            _ -> (CString, Element)
      e <- tokenOf k run
      pure (t, [e])

cExpect :: (CTok -> Bool) -> Text -> P [Elem]
cExpect ok what = do
  tv <- trivia wsTrivia
  t <- peekP (fst <$> lexCompBound)
  if ok t
    then do
      (_, e) <- lexCompBound
      pure (tv ++ e)
    else failHere ("expected " <> what)

-- | @comp_bound ::= ident | ident IN ident | ident IN ident dots ident@,
-- with the given lexer for the identifiers, as a 'CompBound' node.
pCompBoundWith :: P (CTok, [Elem]) -> P [Elem]
pCompBoundWith lexer = do
  i1 <- expect (== CString) "a bound"
  tIn <- peekAfterWs
  body <- case tIn of
    CIn -> do
      kw <- expect (== CIn) "IN"
      i2 <- expect (== CString) "a lower bound"
      tDots <- peekAfterWs
      case tDots of
        CDots -> do
          d <- expect (== CDots) ".."
          i3 <- expect (== CString) "an upper bound"
          pure (kw ++ i2 ++ d ++ i3)
        _ -> pure (kw ++ i2)
    _ -> pure []
  let (es, trailing) = splitTrailing (i1 ++ body)
  pure (tight CompBound es ++ trailing)
  where
    peekAfterWs = peekP (trivia wsTrivia >> (fst <$> lexer))
    expect ok what = do
      tv <- trivia wsTrivia
      t <- peekP (fst <$> lexer)
      if ok t
        then do
          (_, e) <- lexer
          pure (tv ++ e)
        else failHere ("expected " <> what)

------------------------------------------------------------------------
-- Grammar rules and productions (GRAMMAR.md §3.3, §3.4)

ruleStep :: Step
ruleStep _ indent = do
  t <- mPeek
  case t of
    MIdent -> Just <$> pRule indent
    MSym "|" -> failHere "a production outside a grammar rule"
    _
      | endsSection t -> pure Nothing
      | otherwise -> failHere "expected a grammar rule"

pRule :: [Elem] -> P (GreenNode Kind, [Elem])
pRule indent = do
  names <- pNames
  cc <- mSym "::"
  prefix <- mIdent "a production-name prefix"
  cce <- mSym "::="
  homs <- pHoms
  let (header, pending) = splitTrailing (names ++ cc ++ prefix ++ cce ++ homs)
  (prods, leftover) <- itemLoop metaTrivia pending prodStep
  pure (greenNode Rule (indent ++ header ++ prods), leftover)

prodStep :: Step
prodStep _ indent = do
  t <- mPeek
  case t of
    MSym "|" -> Just <$> pProd indent
    MIdent -> pure Nothing
    _
      | endsSection t -> pure Nothing
      | otherwise -> failHere "expected | or the next grammar rule"

pProd :: [Elem] -> P (GreenNode Kind, [Elem])
pProd indent = do
  bar <- mSym "|"
  els <- pElementsUntilColonColon
  cats <- pCategories
  name <- mIdent "a production name"
  bs <- pBindspecGroups
  homs <- pHoms
  pure (greenNode Prod (indent ++ bar ++ els ++ cats ++ name ++ bs ++ homs), [])

-- | Elements in @elements@ mode up to and including the @::@ that switches
-- the lexer back.
pElementsUntilColonColon :: P [Elem]
pElementsUntilColonColon = do
  tv <- trivia wsTrivia
  (t, e) <- lexElement
  case t of
    EEof -> failHere "unexpected end of file (expected ::)"
    EColonColon -> pure (tv ++ e)
    ECompOpen -> do
      comp <- pCompElement e
      ((tv ++ [comp]) ++) <$> pElementsUntilColonColon
    ECompMiddle -> failHere "// outside a comprehension"
    ECompClose -> failHere "/> outside a comprehension"
    _ -> ((tv ++ e) ++) <$> pElementsUntilColonColon

data ETok = EEof | EColonColon | EDots | ECompOpen | ECompMiddle | ECompClose | ECompIn | EString
  deriving (Eq, Show)

-- | The next token of the @elements@ mode (GRAMMAR.md §2.5): a run of
-- non-whitespace, classified exactly.
lexElement :: P (ETok, [Elem])
lexElement = do
  r <- rest
  let run = T.takeWhile (not . isWs) r
  if T.null run
    then pure (EEof, [])
    else do
      let (t, k) = case run of
            "::" -> (EColonColon, ColonColon)
            ".." -> (EDots, Dots)
            "..." -> (EDots, Dots)
            "...." -> (EDots, Dots)
            "</" -> (ECompOpen, CompOpen)
            "//" -> (ECompMiddle, CompMiddle)
            "/>" -> (ECompClose, CompClose)
            "IN" -> (ECompIn, CompIn)
            _
              | T.length run >= 2 && T.head run == '\'' -> (EString, QuotedElement)
              | otherwise -> (EString, Element)
      e <- tokenOf k run
      pure (t, [e])

ePeek :: P ETok
ePeek = peekP (trivia wsTrivia >> (fst <$> lexElement))

eExpect :: (ETok -> Bool) -> Text -> P [Elem]
eExpect ok what = do
  tv <- trivia wsTrivia
  t <- peekP (fst <$> lexElement)
  if ok t
    then do
      (_, e) <- lexElement
      pure (tv ++ e)
    else failHere ("expected " <> what)

-- | After @</@: @element* // comp_bound />@ or @element* // ident // comp_bound />@.
pCompElement :: [Elem] -> P Elem
pCompElement open = do
  inner <- elementsUntilMiddle
  mid <- eExpect (== ECompMiddle) "//"
  i <- eExpect (== EString) "an index or a bound"
  t <- ePeek
  body <- case t of
    ECompMiddle -> do
      mid2 <- eExpect (== ECompMiddle) "//"
      bound <- pCompBoundWith lexAsComp
      pure (i ++ mid2 ++ bound)
    _ -> do
      -- the ident already read is the start of the bound
      more <- boundTail
      let (es, trailing) = splitTrailing (i ++ more)
      pure (tight CompBound es ++ trailing)
  close <- eExpect (== ECompClose) "/>"
  pure (node Comp (open ++ inner ++ mid ++ body ++ close))
  where
    elementsUntilMiddle = do
      t <- ePeek
      case t of
        ECompMiddle -> pure []
        EEof -> failHere "unexpected end of file in a comprehension"
        EColonColon -> failHere ":: inside a comprehension"
        ECompClose -> failHere "/> before //"
        ECompOpen -> do
          tv <- trivia wsTrivia
          (_, e) <- lexElement
          c <- pCompElement e
          ((tv ++ [c]) ++) <$> elementsUntilMiddle
        _ -> do
          tv <- trivia wsTrivia
          (_, e) <- lexElement
          ((tv ++ e) ++) <$> elementsUntilMiddle
    boundTail = do
      t <- ePeek
      case t of
        ECompIn -> do
          kw <- eExpect (== ECompIn) "IN"
          lo <- eExpect (== EString) "a lower bound"
          t2 <- ePeek
          case t2 of
            EDots -> do
              d <- eExpect (== EDots) ".."
              hi <- eExpect (== EString) "an upper bound"
              pure (kw ++ lo ++ d ++ hi)
            _ -> pure (kw ++ lo)
        _ -> pure []
    lexAsComp = do
      (t, e) <- lexElement
      let t' = case t of
            EEof -> CEof
            EDots -> CDots
            ECompOpen -> COpen
            ECompMiddle -> CMiddle
            ECompClose -> CClose
            ECompIn -> CIn
            EString -> CString
            EColonColon -> CString
      pure (t', e)

-- | The categories of a production or definition, up to and including the
-- @::@ that follows them.
pCategories :: P [Elem]
pCategories = do
  t <- mPeek
  case t of
    MIdent -> do
      i <- mIdent "a category"
      (i ++) <$> pCategories
    MSym "::" -> mSym "::"
    _ -> failHere "expected a category or ::"

------------------------------------------------------------------------
-- Binding specifications (GRAMMAR.md §3.5)

-- | Zero or more @(+ ... +)@ groups, each a 'Bindspecs' node.
pBindspecGroups :: P [Elem]
pBindspecGroups = do
  tv <- trivia metaTrivia
  t <- peekP (fst <$> lexMeta)
  case t of
    MSym "(+" -> do
      (_, open) <- lexMeta
      body <- bindspecList
      more <- pBindspecGroups
      pure (tv ++ [node Bindspecs (open ++ body)] ++ more)
    _ -> pure tv
  where
    bindspecList = do
      tv <- trivia bindTrivia
      t <- peekP (fst <$> lexBind)
      case t of
        BClose -> do
          (_, e) <- lexBind
          pure (tv ++ e)
        BEof -> failHere "unclosed (+ (expected +))"
        _ -> do
          b <- pBindspec
          ((tv ++ b) ++) <$> bindspecList

data BTok = BEof | BClose | BKw !Text | BSym !Text | BIdent
  deriving (Eq, Show)

bindKeywords :: [Text]
bindKeywords = ["bind", "in", "names", "distinctnames", "union", "IN"]

bindSymbols :: [(Text, Kind)]
bindSymbols =
  [ ("....", Dots), ("...", Dots), ("+)", BindClose), ("{}", Empty), ("..", Dots)
  , ("</", CompOpen), ("//", CompMiddle), ("/>", CompClose)
  , ("=", Eq), ("#", Hash), ("(", LParen), (")", RParen)
  ]

-- | The next token of the @bindspec@ mode after trivia (GRAMMAR.md §2.8).
lexBind :: P (BTok, [Elem])
lexBind = do
  r <- rest
  if T.null r
    then pure (BEof, [])
    else do
      let identRun = T.takeWhile isIdentChar r
          il = T.length identRun
          sym = find (\(s, _) -> s `T.isPrefixOf` r) bindSymbols
      case sym of
        Just (s, k) | il <= T.length s -> do
          e <- tokenOf k s
          pure (if s == "+)" then BClose else BSym s, [e])
        _
          | il > 0 && identRun `elem` bindKeywords -> do
              e <- tokenOf (if identRun == "IN" then CompIn else Keyword) identRun
              pure (BKw identRun, [e])
          | il > 0 -> do
              e <- tokenOf Ident identRun
              pure (BIdent, [e])
          | otherwise -> failHere ("lexing error in a bindspec: unexpected " <> T.take 1 r)

bPeek :: P BTok
bPeek = peekP (trivia bindTrivia >> (fst <$> lexBind))

bExpect :: (BTok -> Bool) -> Text -> P [Elem]
bExpect ok what = do
  tv <- trivia bindTrivia
  t <- peekP (fst <$> lexBind)
  if ok t
    then do
      (_, e) <- lexBind
      pure (tv ++ e)
    else failHere ("expected " <> what)

bKw :: Text -> P [Elem]
bKw k = bExpect (== BKw k) k

bSym :: Text -> P [Elem]
bSym s = bExpect (== BSym s) s

bIdent :: Text -> P [Elem]
bIdent = bExpect (== BIdent)

pBindspec :: P [Elem]
pBindspec = do
  t <- bPeek
  es <- case t of
    BKw "bind" -> do
      kw <- bKw "bind"
      m <- pMse
      i <- bKw "in"
      nt <- bIdent "a nonterminal"
      pure (kw ++ m ++ i ++ nt)
    BKw "names" -> do
      a <- namesOf
      op <- bExpect (\x -> x == BSym "=" || x == BSym "#") "= or #"
      b <- namesOf
      pure (a ++ op ++ b)
    BKw "distinctnames" -> do
      kw <- bKw "distinctnames"
      lp <- bSym "("
      m <- pMse
      rp <- bSym ")"
      pure (kw ++ lp ++ m ++ rp)
    BIdent -> do
      f <- bIdent "an auxiliary function name"
      eq <- bSym "="
      m <- pMse
      pure (f ++ eq ++ m)
    _ -> failHere "expected a binding specification"
  let (es', trailing) = splitTrailing es
  if null trailing
    then pure (tight Bindspec es')
    else failHere "internal error: trailing trivia in a bindspec"
  where
    namesOf = do
      kw <- bKw "names"
      lp <- bSym "("
      m <- pMse
      rp <- bSym ")"
      pure (kw ++ lp ++ m ++ rp)

-- | A metavariable set expression, right-associative in @union@, as an
-- 'Mse' node (without trailing trivia).
pMse :: P [Elem]
pMse = do
  a <- mseAtom
  t <- bPeek
  case t of
    BKw "union" -> do
      u <- bKw "union"
      b <- pMse
      pure (tight Mse (tight Mse a ++ u ++ b))
    _ -> pure (tight Mse a)
  where
    mseAtom = do
      t <- bPeek
      case t of
        BSym "{}" -> bSym "{}"
        BSym "</" -> bComp
        BIdent -> do
          i <- bIdent "an identifier"
          t2 <- bPeek
          case t2 of
            BSym ".." -> dotsTail i
            BSym "..." -> dotsTail i
            BSym "...." -> dotsTail i
            BSym "(" -> do
              lp <- bSym "("
              t3 <- bPeek
              arg <- case t3 of
                BSym "</" -> bComp
                BIdent -> do
                  j <- bIdent "an argument"
                  t4 <- bPeek
                  case t4 of
                    BSym ".." -> dotsTail j
                    BSym "..." -> dotsTail j
                    BSym "...." -> dotsTail j
                    _ -> pure j
                _ -> failHere "expected an argument"
              rp <- bSym ")"
              pure (i ++ lp ++ arg ++ rp)
            BSym "</" -> (i ++) <$> bComp
            _ -> pure i
        _ -> failHere "expected a metavariable set expression"
    dotsTail i = do
      d <- bExpect isDots ".."
      j <- bIdent "an identifier after the dots"
      pure (i ++ d ++ j)
    isDots x = x == BSym ".." || x == BSym "..." || x == BSym "...."
    -- </ ident // comp_bound />
    bComp = do
      open <- bSym "</"
      i <- bIdent "an identifier"
      mid <- bSym "//"
      bound <- pCompBoundWith lexAsComp
      close <- bSym "/>"
      pure (open ++ i ++ mid ++ bound ++ close)
    lexAsComp = do
      tv <- trivia bindTrivia
      (t, e) <- lexBind
      let t' = case t of
            BEof -> CEof
            BSym ".." -> CDots
            BSym "..." -> CDots
            BSym "...." -> CDots
            BSym "</" -> COpen
            BSym "//" -> CMiddle
            BSym "/>" -> CClose
            BKw "IN" -> CIn
            BIdent -> CString
            _ -> CEof
      pure (t', tv ++ e)

------------------------------------------------------------------------
-- Embedded code (GRAMMAR.md §3.7)

embedStep :: Step
embedStep _ indent = do
  t <- mPeek
  case t of
    MSym "{{" -> Just <$> embed False
    MSym "{{*" -> Just <$> embed True
    _
      | endsSection t -> pure Nothing
      | otherwise -> failHere "expected {{ in an embed section"
  where
    embed star = do
      (_, open) <- lexMeta
      body <- homBody star EmbedBody
      pure (greenNode Embed (indent ++ open ++ body), [])

------------------------------------------------------------------------
-- Subrules, context rules, substitutions, free variables (GRAMMAR.md §3.8)

subruleStep :: Step
subruleStep = declStep Subrule "a subrule declaration" $ do
  lo <- mIdent "a nonterminal root"
  op <- mSym "<::"
  hi <- mIdent "a nonterminal root"
  homs <- pHoms
  pure (lo ++ op ++ hi ++ homs)

contextruleStep :: Step
contextruleStep = declStep Contextrule "a context rule declaration" $ do
  e <- mIdent "a context nonterminal root"
  op <- mSym "_::"
  target <- mIdent "a nonterminal root"
  cc <- mSym "::"
  hole <- mIdent "a nonterminal root"
  pure (e ++ op ++ target ++ cc ++ hole)

freevarStep :: Step
freevarStep = declStep Freevar "a free variable declaration" $ do
  this <- mIdent "a nonterminal root"
  that <- mIdent "a metavariable or nonterminal root"
  cc <- mSym "::"
  name <- mIdent "a function name"
  homs <- pHoms
  pure (this ++ that ++ cc ++ name ++ homs)

substitutionStep :: Step
substitutionStep _ indent = do
  t <- mPeek
  case t of
    MKw k | k == "single" || k == "multiple" -> do
      kw <- mKw k
      this <- mIdent "a nonterminal root"
      that <- mIdent "a metavariable or nonterminal root"
      cc <- mSym "::"
      name <- mIdent "a function name"
      homs <- pHoms
      pure (Just (greenNode Substitution (indent ++ kw ++ this ++ that ++ cc ++ name ++ homs), []))
    _
      | endsSection t -> pure Nothing
      | otherwise -> failHere "expected single or multiple"

-- | A declaration that starts with an identifier.
declStep :: Kind -> Text -> P [Elem] -> Step
declStep kind what body _ indent = do
  t <- mPeek
  case t of
    MIdent -> do
      es <- body
      pure (Just (greenNode kind (indent ++ es), []))
    _
      | endsSection t -> pure Nothing
      | otherwise -> failHere ("expected " <> what)

------------------------------------------------------------------------
-- Parsing priorities and hom sections (GRAMMAR.md §3.11, §3.12)

parsingStep :: Step
parsingStep = declStep ParsingAnnotation "a parsing annotation" $ do
  a <- mIdent "a production name"
  op <- mExpect isOp "<=, left, right or non"
  b <- mIdent "a production name"
  pure (a ++ op ++ b)
  where
    isOp t = t == MSym "<=" || t == MKw "left" || t == MKw "right" || t == MKw "non"

homsItemStep :: Step
homsItemStep _ indent = do
  t <- mPeek
  case t of
    MSym "::" -> do
      cc <- mSym "::"
      name <- mIdent "a production name"
      bs <- pBindspecGroups
      homs <- pHoms
      pure (Just (greenNode HomsItem (indent ++ cc ++ name ++ bs ++ homs), []))
    _
      | endsSection t -> pure Nothing
      | otherwise -> failHere "expected :: in a homs section"

------------------------------------------------------------------------
-- Inductive definitions (GRAMMAR.md §3.9, §4)

pDefns :: [Elem] -> P (GreenNode Kind, [Elem])
pDefns indent = do
  kw <- mKw "defns"
  name <- mIdent "a definition class name"
  cc <- mSym "::"
  prefix <- mIdent "a rule-name prefix"
  cce <- mSym "::="
  homs <- pHoms
  let (header, pending) = splitTrailing (kw ++ name ++ cc ++ prefix ++ cce ++ homs)
  (defns, leftover) <- itemLoop metaTrivia pending defnStep
  pure (greenNode Defns (indent ++ header ++ defns), leftover)

defnStep :: Step
defnStep _ indent = do
  t <- mPeek
  case t of
    MKw "defn" -> Just <$> pDefn indent
    _
      | endsSection t -> pure Nothing
      | otherwise -> failHere "expected defn"

pDefn :: [Elem] -> P (GreenNode Kind, [Elem])
pDefn indent = do
  kw <- mKw "defn"
  form <- pElementsUntilColonColon
  cats <- pCategories
  name <- mIdent "a definition name"
  cc <- mSym "::"
  prefix <- mIdent "a rule-name prefix"
  homs <- pHoms
  by <- mKw "by"
  (body, leftover) <- defnBody
  pure (greenNode Defn (indent ++ kw ++ form ++ cats ++ name ++ cc ++ prefix ++ homs ++ by ++ body), leftover)

-- | One line of a rule body (GRAMMAR.md §2.9), with its tokens.
data LineUnit
  = LUBlank [Elem]
  -- ^ @Space? Newline@
  | LUComment [Elem]
  -- ^ @Space? LineComment Newline?@
  | LUBlock [Elem]
  -- ^ @Space? BlockComment@; the rest of its last line is the next unit
  | LUDashes [Elem] [Elem]
  -- ^ indentation, then the 'RuleLine' node's children: dashes and the
  -- annotation; followed by a newline unit if there is one
  | LUText [Elem] Elem (Maybe Text)
  -- ^ indentation, the 'Line' token, and the keyword if the first word is
  -- one (the unit then ends the body and is not consumed)
  | LUEof

-- | Classify and consume the line at the current position. Keyword lines
-- are not consumed.
lineUnit :: P LineUnit
lineUnit = do
  r <- rest
  if T.null r
    then pure LUEof
    else do
      let line = T.takeWhile (not . isNl) r
          after = T.drop (T.length line) r
          hasNl = not (T.null after)
          ind = T.takeWhile isNnws line
          body = T.drop (T.length ind) line
          indentTok = if T.null ind then pure [] else (: []) <$> tokenOf Space ind
          newline = if hasNl then (: []) <$> newlineToken after else pure []
      if
        | T.null body && hasNl -> do
            i <- indentTok
            nl <- newline
            pure (LUBlank (i ++ nl))
        | T.null body -> do
            -- whitespace only, at end of file: Ott takes it as a LINE
            i <- if T.null ind then failHere "internal error" else tokenOf Line ind
            pure (LUText [] i Nothing)
        | "%" `T.isPrefixOf` body -> do
            i <- indentTok
            cm <- tokenOf LineComment body
            nl <- newline
            pure (LUComment (i ++ [cm] ++ nl))
        | ">>" `T.isPrefixOf` body && T.all isNnws (T.drop 2 body) && hasNl -> do
            i <- indentTok
            bc <- blockComment (T.drop (T.length ind) r)
            pure (LUBlock (i ++ [bc]))
        | "----" `T.isPrefixOf` body -> do
            let dashRun = T.length (T.takeWhile (== '-') body)
                dashes
                  | dashRun == T.length body = dashRun - 1
                  | otherwise = dashRun
            if dashRun == 4 && dashRun == T.length body
              then textUnit ind body indentTok
              else do
                i <- indentTok
                d <- tokenOf Dashes (T.take dashes body)
                annot <- withinLine pRuleAnnotation
                pure (LUDashes i (d : annot))
        | otherwise -> textUnit ind body indentTok
  where
    textUnit _ind body indentTok = do
      let w = T.takeWhile (not . isWs) body
          restWords = T.dropWhile isWs (T.drop (T.length w) body)
          w2 = T.takeWhile (not . isWs) restWords
          kw
            | w `elem` itemKeywords || w == "defn" || w == "fun" = Just w
            | w == "{{com" = Just "{{com"
            | w == "{{" && w2 == "com" = Just "{{ com"
            | otherwise = Nothing
      case kw of
        Just k -> do
          -- not consumed; the caller decides
          pure (LUText [] (Token (greenToken Line body)) (Just k))
        Nothing -> do
          i <- indentTok
          l <- tokenOf Line body
          pure (LUText i l Nothing)

-- | The annotation after the dashes: @ident* :: ident hom*@ to the end of
-- the line, parsed with the @metalang@ lexer.
pRuleAnnotation :: P [Elem]
pRuleAnnotation = do
  cats <- pCategories
  name <- mIdent "a rule name"
  homs <- pHoms
  tv <- trivia metaTrivia
  t <- peekP (fst <$> lexMeta)
  case t of
    MEof -> pure (cats ++ name ++ homs ++ tv)
    _ -> failHere "unexpected text after the rule name"

-- | The body of a definition after @by@: blocks of lines separated by blank
-- lines (GRAMMAR.md §4). Returns the children and the trailing trivia.
defnBody :: P ([Elem], [Elem])
defnBody = go 0 Nothing [] []
  where
    -- blanks: blank lines seen since the last block; prev: the last rule
    -- awaiting its trailing trivia; acc: finished children; pending: trivia
    -- not yet placed.
    go :: Int -> Maybe (GreenNode Kind, Maybe Int) -> [Elem] -> [Elem] -> P ([Elem], [Elem])
    go blanks prev acc pending = do
      u <- peekP lineUnit
      case u of
        LUEof -> finish prev acc pending
        LUText _ _ (Just k)
          | k == "{{com" || k == "{{ com" -> do
              requireBlank blanks
              es <- defnCom
              let (acc', pending') = flush prev acc pending
              go 0 Nothing (acc' ++ pending' ++ [node DefnCom es]) []
          | otherwise -> finish prev acc pending
        LUBlank es -> lineUnit >> go (blanks + 1) prev acc (pending ++ es)
        LUBlock es -> lineUnit >> go blanks prev acc (pending ++ es)
        _ -> do
          requireBlank blanks
          let (acc', pending') = flush prev acc pending
          block <- pBlock
          case block of
            Left triv -> go 0 Nothing acc' (pending' ++ triv)
            Right (before, n, col, trailing) ->
              go 0 (Just (n, col)) (acc' ++ pending' ++ before) trailing
    requireBlank blanks =
      if blanks == 0 then failHere "a rule must be preceded by a blank line" else pure ()
    flush prev acc pending = case prev of
      Nothing -> (acc, pending)
      Just (n, col) ->
        let (n', remaining) = attach col n pending
         in (acc ++ [Node n'], remaining)
    finish prev acc pending =
      let (acc', pending') = flush prev acc pending
       in pure (acc', pending')
    -- {{com or {{ com, then an embed body to }}; the rest of the line is the
    -- next unit
    defnCom = do
      r <- rest
      let ind = T.takeWhile isNnws r
      i <- if T.null ind then pure [] else (: []) <$> tokenOf Space ind
      open <- tokenOf HomOpen "{{"
      sp <- trivia wsTrivia
      com <- tokenOf HomText "com"
      body <- homBody False DefnComBody
      pure (i ++ [open] ++ sp ++ [com] ++ body)

-- | A block of lines: either trivia only, or the trivia before the rule
-- (which belongs to the definition), the rule, its column, and the trivia
-- after its last line.
pBlock :: P (Either [Elem] ([Elem], GreenNode Kind, Maybe Int, [Elem]))
pBlock = collect [] Nothing [] Nothing
  where
    -- before: trivia before the rule starts; mstart: the rule's column once
    -- it has started; items: children so far; dashes: whether a RuleLine
    -- has been seen
    collect before mstart items dashes = do
      u <- peekP lineUnit
      case u of
        LUComment es -> do
          _ <- lineUnit
          addTrivia before mstart items dashes es
        LUBlock es -> do
          _ <- lineUnit
          addTrivia before mstart items dashes es
        LUText i l Nothing -> do
          _ <- lineUnit
          nl <- newlineAfter
          let kind = case dashes of
                Nothing -> Premise
                Just _ -> Conclusion
              item = node kind (i ++ [l])
          collect before (startCol mstart i) (items ++ [item] ++ nl) dashes
        LUDashes i es -> do
          _ <- lineUnit
          nl <- newlineAfter
          case dashes of
            Just _ -> failHere "a second dashed line in the same rule"
            Nothing -> do
              let item = node RuleLine (i ++ es)
              collect before (startCol mstart i) (items ++ [item] ++ nl) (Just ())
        _ -> done before mstart items dashes
    addTrivia before mstart items dashes es = case mstart of
      Nothing -> collect (before ++ es) mstart items dashes
      Just _ -> collect before mstart (items ++ es) dashes
    startCol mstart i = case mstart of
      Just c -> Just c
      Nothing -> Just (sum (map elementTextLength i))
    newlineAfter = do
      r <- rest
      if not (T.null r) && isNl (T.head r) then (: []) <$> newlineToken r else pure []
    done before mstart items dashes = case mstart of
      Nothing -> pure (Left (before ++ items))
      Just col ->
        let (body, trailing) = splitTrailing items
            n = case dashes of
              Just _ -> greenNode DRule body
              Nothing -> greenNode Lineless (map toFormula body)
         in pure (Right (before, n, Just col, trailing))
    toFormula e = case e of
      Node n | nodeKind n == Premise -> node Formula (nodeChildren n)
      _ -> e

------------------------------------------------------------------------
-- Functions (GRAMMAR.md §3.10)

pFuns :: [Elem] -> P (GreenNode Kind, [Elem])
pFuns indent = do
  kw <- mKw "funs"
  name <- mIdent "a function class name"
  cce <- mSym "::="
  homs <- pHoms
  let (header, pending) = splitTrailing (kw ++ name ++ cce ++ homs)
  (funs, leftover) <- itemLoop metaTrivia pending funStep
  pure (greenNode Funs (indent ++ header ++ funs), leftover)

funStep :: Step
funStep _ indent = do
  t <- mPeek
  case t of
    MKw "fun" -> Just <$> pFundefn indent
    _
      | endsSection t -> pure Nothing
      | otherwise -> failHere "expected fun"

pFundefn :: [Elem] -> P (GreenNode Kind, [Elem])
pFundefn indent = do
  kw <- mKw "fun"
  form <- pElementsUntilColonColon
  result <- mIdent "a result nonterminal"
  cc <- mSym "::"
  name <- mIdent "a function name"
  homs <- pHoms
  by <- mKw "by"
  (body, leftover) <- funBody
  pure (greenNode Fundefn (indent ++ kw ++ form ++ result ++ cc ++ name ++ homs ++ by ++ body), leftover)

-- | After @by@: a blank line, then clauses, comments and blank lines until a
-- keyword line.
funBody :: P ([Elem], [Elem])
funBody = do
  u <- peekP lineUnit
  first <- case u of
    LUBlank es -> lineUnit >> pure es
    _ -> failHere "fun ... by must be followed by a blank line"
  go Nothing [] first
  where
    go prev acc pending = do
      u <- peekP lineUnit
      case u of
        LUEof -> finish prev acc pending
        LUText _ _ (Just _) -> finish prev acc pending
        LUBlank es -> lineUnit >> go prev acc (pending ++ es)
        LUComment es -> lineUnit >> go prev acc (pending ++ es)
        LUBlock es -> lineUnit >> go prev acc (pending ++ es)
        LUDashes _ _ -> failHere "a dashed line in a function definition"
        LUText i l Nothing -> do
          _ <- lineUnit
          r <- rest
          nl <- if not (T.null r) && isNl (T.head r) then (: []) <$> newlineToken r else pure []
          let (acc', pending') = flush prev acc pending
              col = Just (sum (map elementTextLength i))
          go (Just (greenNode Clause (i ++ [l]), col)) (acc' ++ pending') nl
    flush prev acc pending = case prev of
      Nothing -> (acc, pending)
      Just (n, col) ->
        let (n', remaining) = attach col n pending
         in (acc ++ [Node n'], remaining)
    finish prev acc pending = pure (flush prev acc pending)

-- | The UTF-8 length of a text, in constant time.
byteLen :: Text -> Int
byteLen = TF.lengthWord8
