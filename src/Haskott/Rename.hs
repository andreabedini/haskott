{-# LANGUAGE OverloadedStrings #-}

-- | Renaming a root: a metavariable, index variable or grammar-rule name,
-- everywhere it occurs in a specification and in the @[[ ]]@ quotations
-- of documents filtered against it.
--
-- The occurrences are found on the lossless trees after the term splice,
-- so that rule lines are known token by token: declarations, production
-- and judgement elements, comprehension bounds, binding specifications,
-- hom references, subrules, context rules, substitutions, free
-- variables, function results, the terms of rule lines, and the
-- quotations of embeds, comment blocks and documents. An identifier is
-- renamed when Ott's identifier lexer reads it as the root with a suffix,
-- or as another root with a suffix that mentions the index variable being
-- renamed. Every other byte is left alone: comments, hom bodies and
-- target text are not touched.
--
-- Every rename is checked before it is returned. The renamed files are
-- loaded, checked and parsed again, and they must give the same grammar
-- and the same parses of every term, up to the renaming. This refuses a
-- new name that captures other identifiers, clashes with a terminal, or
-- changes how anything parses.
module Haskott.Rename
  ( Edit (..)
  , Problem (..)
  , FileRename (..)
  , renameRoot
  , renameableRoots
  , validNewName
  , applyEdits
    -- * Looking roots up
  , Index
  , indexSpec
  , indexRenameable
  , indexRoots
  , indexTree
  , occurrences
  , declarations
  , rootAt
  ) where

import Control.Monad (unless, when)
import qualified Data.ByteString as B
import Data.Char (isAlpha, isAlphaNum)
import Data.List (nub, sortOn, unfoldr)
import qualified Data.Set as Set
import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Text.Encoding as TE
import Graft
import qualified Graft.Cursor as Cursor
import qualified Graft.Green as Green
import qualified Graft.Range as Range
import Haskott.Load
import Haskott.Spec
import Haskott.Syntax (ParseError (..))
import qualified Data.Map.Strict as M
import Data.Maybe (mapMaybe)
import Haskott.Syntax.Ast (identValue)
import qualified Haskott.Syntax.Ast as A
import Haskott.Syntax.Kind (Kind)
import qualified Haskott.Syntax.Kind as K
import Haskott.Syntax.Parser (metaKeywords)
import Haskott.Term.Parse
import Haskott.Term.Requests (TermRequest (..), termRequests)
import Haskott.Term.Splice (spliceTerms)
import Haskott.Term.Symterm
import Haskott.Term.Tree (termElements)
import Haskott.Tex (documentQuotations)

-- | Replace the bytes from start to end.
data Edit = Edit
  { editStart :: Int
  , editEnd :: Int
  , editOld :: Text
  , editNew :: Text
  }
  deriving (Eq, Show)

-- | A reason not to rename, located in a file when it can be.
data Problem = Problem
  { problemWhere :: Maybe (FilePath, Text, Int)
  -- ^ the file, its text, and the byte offset
  , problemMessage :: Text
  }

data FileRename = FileRename
  { frPath :: FilePath
  , frOld :: Text
  , frNew :: Text
  , frEdits :: [Edit]
  , frNotes :: [(Int, Text)]
  -- ^ mentions left as written, in comments and hom bodies, which are
  -- target text: their offsets in the old text, and the words
  }

-- | Rename a root in the specification files (in the order Ott reads
-- them) and in the documents filtered against them.
renameRoot :: Text -> Text -> [(FilePath, Text)] -> [(FilePath, Text)] -> Either [Problem] [FileRename]
renameRoot old new specFiles docFiles = do
  loaded <- either (Left . pure . loadProblem "") Right (loadSpec specFiles)
  let spec = ldSpec loaded
  validate spec old new
  let tp = makeTermParser spec
      ctx = Ctx old new (specRoots spec) tp (M.unions (map (namedOwners . srcTree) (ldSources loaded)))
      specResults =
        [ (srcPath s, srcText s, treeEdits ctx s tree', mentions ctx (srcTree s))
        | s <- ldSources loaded
        , let (tree', _, _) = spliceTerms (FirstIfSame []) tp (srcTree s)
        ]
      docResults = [(f, src, docEdits ctx f src, []) | (f, src) <- docFiles]
      problems = concat [ps | (_, _, (ps, _), _) <- specResults ++ docResults]
  unless (null problems) (Left problems)
  let renamed = [FileRename f src (applyEdits src es) es notes | (f, src, (_, es), notes) <- specResults ++ docResults]
      nSpec = length specFiles
      newSpecFiles = [(frPath r, frNew r) | r <- take nSpec renamed]
      newDocFiles = [(frPath r, frNew r) | r <- drop nSpec renamed]
  verify old new spec tp docFiles newSpecFiles newDocFiles
  pure renamed

loadProblem :: Text -> LoadError -> Problem
loadProblem prefix e = case e of
  LoadParse f src pe -> Problem (Just (f, src, parseErrorOffset pe)) (prefix <> parseErrorMessage pe)
  LoadCheck f src d -> Problem (Just (f, src, fromIntegral (Range.start (diagRange d)))) (prefix <> diagMessage d)

------------------------------------------------------------------------
-- What may be renamed

specialRules :: [Text]
specialRules = ["formula", "judgement", "user_syntax", "terminals"]

specRoots :: Spec -> Roots
specRoots spec =
  Roots
    { rootsNonindexMetavars = [n | md <- specMetavars spec, not (mvdIndexvar md), (n, _) <- mvdNames md]
    , rootsIndexvars = specIndexvars spec
    , rootsNonterms = [n | r <- specRules spec, (n, _) <- ruleNames r]
    }

-- | The old name must be a root the user declared; the new one must be a
-- plain identifier that is no root, keyword or special rule.
validate :: Spec -> Text -> Text -> Either [Problem] ()
validate spec old new = do
  let mvrs = [n | md <- specMetavars spec, (n, _) <- mvdNames md]
      userRules = [r | r <- specRules spec, not (ruleJudgement r), ruleName r `notElem` specialRules]
      userNtrs = [n | r <- userRules, (n, _) <- ruleNames r]
      allNtrs = [n | r <- specRules spec, (n, _) <- ruleNames r]
      bad m = Left [Problem Nothing m]
  when (old == new) (bad "the old and the new name are the same")
  unless (old `elem` mvrs || old `elem` userNtrs) $
    if old `elem` allNtrs
      then bad (quote old <> " names a judgement or a rule Ott synthesises; only metavariables, index variables and grammar rules can be renamed")
      else bad (quote old <> " is not a metavariable, index variable or nonterminal root of the specification")
  unless (validIdent new) $
    bad (quote new <> " is not a plain root: use letters, digits and underscores, starting and ending with a letter")
  when (isKeyword new) (bad (quote new <> " is a keyword of the Ott metalanguage"))
  when (new `elem` specialRules) (bad (quote new <> " is the name of a rule Ott treats specially"))
  when (new `elem` mvrs || new `elem` allNtrs) (bad (quote new <> " is already a root of the specification"))
  when (new `elem` terminals) (bad (quote new <> " is a terminal of the grammar, so it would read as the root wherever it is used"))
  where
    terminals = [t | r <- specRules spec, p <- ruleProds r, e <- prodElements p, t <- elementTerminals e]
    elementTerminals e = case e of
      Terminal t -> [t]
      ListForm lb -> maybe [] pure (lbSeparator lb) ++ concatMap elementTerminals (lbElements lb)
      _ -> []


-- | The names that may be renamed: metavariables, index variables and
-- the names of the user's grammar rules.
renameableRoots :: Spec -> [Text]
renameableRoots spec =
  [n | md <- specMetavars spec, (n, _) <- mvdNames md]
    ++ [n | r <- specRules spec, not (ruleJudgement r), ruleName r `notElem` specialRules, (n, _) <- ruleNames r]

validIdent :: Text -> Bool
validIdent t = case (T.uncons t, T.unsnoc t) of
  (Just (c, _), Just (_, l)) -> isAlpha c && isAlpha l && T.all (\x -> isAlphaNum x || x == '_') t
  _ -> False

isKeyword :: Text -> Bool
isKeyword t = t `elem` metaKeywords || t == "IN"

-- | Whether a name can be given to a root, before looking at the
-- specification: a plain identifier, not a keyword or a special rule.
validNewName :: Text -> Bool
validNewName t = validIdent t && not (isKeyword t) && t `notElem` specialRules

quote :: Text -> Text
quote t = "\"" <> t <> "\""

------------------------------------------------------------------------
-- Finding the occurrences

data Ctx = Ctx
  { cOld :: Text
  , cNew :: Text
  , cRoots :: Roots
  , cParser :: TermParser
  , cOwners :: M.Map Text (Set.Set Text)
  -- ^ the identifiers of each production and judgement form, by full
  -- name, for the homs that hom sections attach to them
  }

type C = Cursor Kind

-- | The edits of one specification file, from its spliced tree.
treeEdits :: Ctx -> Source -> GreenNode Kind -> ([Problem], [Edit])
treeEdits ctx s tree = mconcat (map (visit [] Set.empty) (Cursor.children (Cursor.fromGreen (Node tree))))
  where
    file = srcPath s
    text = srcText s
    problemAt off m = Problem (Just (file, text, off)) m

    -- owner: the identifiers a hom reference can resolve to, those of the
    -- elements of the enclosing production, judgement form or function,
    -- or the names of the enclosing declaration; a reference that names
    -- none of them is target text, not a root
    visit :: [Kind] -> Set.Set Text -> C -> ([Problem], [Edit])
    visit anc owner c = case Cursor.green c of
      Token t -> tokenEdits anc owner c t
      Node _
        | Cursor.kind c == K.HomRef && (K.Embed `elem` anc || K.DefnCom `elem` anc) && not (spliced c) -> quotationEdits c
        | otherwise ->
            let owner' = case Cursor.kind c of
                  k | k `elem` [K.Prod, K.Defn, K.Fundefn, K.MetavarDecl, K.Rule] -> ownerIdents c
                  K.DRule -> Set.empty
                  K.HomsItem -> case (castNode c, Cursor.parent c >>= castNode) of
                    (Just item, Just section) -> M.findWithDefault Set.empty (A.homsSectionWrapper section <> A.homsItemName item) (cOwners ctx)
                    _ -> Set.empty
                  _ -> owner
             in mconcat (map (visit (Cursor.kind c : anc) owner') (Cursor.children c))



    spliced c = any (isTermKind . Cursor.kind) (Cursor.children c)
    isTermKind k = case k of
      K.TNode _ _ -> True
      K.TNonterm -> True
      K.TMetavar -> True
      K.TList -> True
      _ -> False

    tokenEdits anc owner c t =
      let k = Green.tokenKind t
          v = Green.text t
          start = fromIntegral (Range.start (Cursor.range c))
          end = fromIntegral (Range.end (Cursor.range c))
          parent = case anc of (p : _) -> Just p; [] -> Nothing
          grand = case anc of (_ : g : _) -> Just g; _ -> Nothing
          one r = case r of
            Left m -> ([problemAt start m], [])
            Right Nothing -> ([], [])
            Right (Just v') -> ([], [Edit start end v v'])
          exact = one (Right (renameExact ctx v))
          lexed = one (renameLexed ctx Nothing v)
       in case k of
            K.TNonterm -> one (renameLexed ctx (Just True) v)
            K.TMetavar -> one (renameTermMetavar ctx v)
            K.TIndex -> one (Right (renameIndex ctx v))
            K.Line
              | parent == Just K.Formula -> lineEdits start v
              | cOld ctx `T.isInfixOf` v ->
                  ([problemAt start ("this rule line does not parse, so " <> quote (cOld ctx) <> " cannot be renamed in it")], [])
              | otherwise -> ([], [])
            K.Ident
              | parent == Just K.Name && grand `elem` [Just K.MetavarDecl, Just K.Rule] -> exact
              | K.Bindspecs `elem` anc -> if auxFunction c then ([], []) else lexed
              | parent `elem` [Just K.Subrule, Just K.Contextrule] -> exact
              | parent `elem` [Just K.Substitution, Just K.Freevar] && colonsBefore c == 0 -> exact
              | parent == Just K.Fundefn && colonsBefore c == 1 -> exact
              | parent == Just K.HomsItem && identValue v == cOld ctx ->
                  ([problemAt start "a hom section names this root; rename does not support hom sections yet"], [])
              | otherwise -> ([], [])
            K.Element
              | K.HomRef `elem` anc -> if v `Set.member` owner then lexed else ([], [])
              | any (`elem` anc) [K.Prod, K.Defn, K.Fundefn, K.Comp, K.CompBound] -> lexed
              | otherwise -> ([], [])
            K.QuotedElement
              | any (`elem` anc) [K.Prod, K.Defn, K.Fundefn, K.Comp] -> one (Right (renameQuoted ctx v))
              | otherwise -> ([], [])
            K.HomText
              | parent == Just K.CompBound -> lexed
              | K.HomRef `elem` anc && v `Set.member` owner -> lexed
              | otherwise -> ([], [])
            _ -> ([], [])

    colonsBefore c = length [() | p <- prevSiblings c, Cursor.kind p == K.ColonColon]
    -- an auxiliary function, applied as in f(x) or defined as in f = x
    auxFunction c = case filter (not . trivia . Cursor.kind) (nextSiblings c) of
      (n : _) -> Cursor.kind n `elem` [K.LParen, K.Eq]
      [] -> False
    nextSiblings = unfoldr (\x -> fmap (\n -> (n, n)) (Cursor.nextSibling x))
    trivia k = k `elem` [K.Space, K.Newline, K.LineComment, K.BlockComment]
    prevSiblings = unfoldr (\x -> fmap (\p -> (p, p)) (Cursor.previousSibling x))

    -- a lineless block's line is parsed on its own
    lineEdits start v = case termEdits ctx "formula" userSyntaxTransform v of
      Right es -> ([], map (shiftEdit start) es)
      Left m -> ([problemAt start m], [])

    -- the quotation of an embed or comment block, parsed as user syntax
    quotationEdits c =
      let inner = [x | x <- Cursor.children c, Cursor.kind x /= K.RefOpen, Cursor.kind x /= K.RefClose]
          q = T.concat (map (Green.render . Cursor.green) inner)
          start = case inner of
            (x : _) -> fromIntegral (Range.start (Cursor.range x))
            [] -> fromIntegral (Range.end (Cursor.range c))
       in case termEdits ctx "user_syntax" userSyntaxTransform q of
            Right es -> ([], map (shiftEdit start) es)
            Left m -> ([problemAt start m], [])

-- | The words of comments and hom bodies that read as the root, or as a
-- root whose suffix mentions it: they are target text and stay as
-- written, but the user may want to look at them.
mentions :: Ctx -> GreenNode Kind -> [(Int, Text)]
mentions ctx tree =
  [ (fromIntegral (Range.start (Cursor.range c)) + off, w)
  | c <- Cursor.descendants (Cursor.fromGreen (Node tree))
  , Token t <- [Cursor.green c]
  , isTarget c (Green.tokenKind t)
  , (off, w) <- identWords (Green.text t)
  , involvesRoot ctx w
  ]
  where
    isTarget c k = case k of
      K.LineComment -> True
      K.BlockComment -> True
      K.HomText -> case Cursor.parent c of
        Just p -> Cursor.kind p `elem` [K.Hom, K.Embed, K.DefnCom]
        Nothing -> False
      _ -> False

-- | The maximal runs of identifier characters, with byte offsets.
identWords :: Text -> [(Int, Text)]
identWords = go 0
  where
    isWordChar x = isAlphaNum x || x == '_' || x == '\''
    go off t
      | T.null t = []
      | otherwise =
          let (gap, rest) = T.break isWordChar t
              (w, rest') = T.span isWordChar rest
              off' = off + byteLength gap
           in if T.null w then [] else (off', w) : go (off' + byteLength w) rest'

involvesRoot :: Ctx -> Text -> Bool
involvesRoot ctx w = case renameLexed ctx Nothing w of
  Right (Just _) -> True
  Left _ -> True
  Right Nothing -> False

-- | The identifiers a hom reference under a node can resolve to: the
-- elements of a production, judgement form or function, or the names of
-- a declaration, outside its homs.
ownerIdents :: C -> Set.Set Text
ownerIdents c =
  Set.fromList
    [ Green.text t
    | d <- Cursor.descendants c
    , Token t <- [Cursor.green d]
    , Green.tokenKind t `elem` [K.Element, K.QuotedElement] || (Green.tokenKind t == K.Ident && fmap Cursor.kind (Cursor.parent d) == Just K.Name)
    , K.Hom `notElem` map Cursor.kind (Cursor.ancestors d)
    ]

-- | The owners of the productions and judgement forms of a tree, by the
-- full names hom sections use.
namedOwners :: GreenNode Kind -> M.Map Text (Set.Set Text)
namedOwners tree =
  M.fromList $
    [ (A.rulePrefix r <> A.prodName p, ownerIdents (nodeSyntax p))
    | A.ItemGrammar g <- items
    , r <- A.grammarRules g
    , p <- A.ruleProds r
    ]
      ++ [ (A.defnsWrapper ds <> A.defnName d, ownerIdents (nodeSyntax d))
         | A.ItemDefns ds <- items
         , d <- A.defnsDefns ds
         ]
  where
    items = mapMaybe A.castItem (Cursor.children (Cursor.fromGreen (Node tree)))

shiftEdit :: Int -> Edit -> Edit
shiftEdit n e = e {editStart = editStart e + n, editEnd = editEnd e + n}

-- | The edits of a document, from its quotations.
docEdits :: Ctx -> FilePath -> Text -> ([Problem], [Edit])
docEdits ctx file src = case documentQuotations src of
  Left m -> ([Problem (Just (file, src, 0)) m], [])
  Right qs -> mconcat (map quotation qs)
  where
    quotation (off, written, parsed)
      | written /= parsed && cOld ctx `T.isInfixOf` written =
          ([Problem (Just (file, src, off)) "this quotation contains bracket escapes; rename does not support them"], [])
      | otherwise = case termEdits ctx "user_syntax" userSyntaxTransform written of
          Right es -> ([], map (shiftEdit off) es)
          Left m -> ([Problem (Just (file, src, off)) m], [])

-- | The edits of a term, with offsets in its text. A term with no parse
-- is refused only when it may mention the root.
termEdits :: Ctx -> Text -> Transform -> Text -> Either Text [Edit]
termEdits ctx root transform q =
  let tp = cParser ctx
      stripped = stripTrailingWhitespace q
   in case selectParse (FirstIfSame []) (transform (parseComplete tp root False q)) of
        Nothing
          | cOld ctx `T.isInfixOf` q -> Left ("this term does not parse as " <> root <> ", so " <> quote (cOld ctx) <> " cannot be renamed in it")
          | otherwise -> Right []
        Just p -> do
          let toks = flatten 0 (termElements (termGrammar tp) stripped (parseTree p))
          fmap concat . mapM (tokEdit) $ toks
  where
    tokEdit (off, k, v) =
      let r = case k of
            K.TNonterm -> renameLexed ctx (Just True) v
            K.TMetavar -> renameTermMetavar ctx v
            K.TIndex -> Right (renameIndex ctx v)
            _ -> Right Nothing
       in case r of
            Left m -> Left m
            Right Nothing -> Right []
            Right (Just v') -> Right [Edit off (off + byteLength v) v v']
    flatten :: Int -> [GreenElement Kind] -> [(Int, Kind, Text)]
    flatten _ [] = []
    flatten off (el : rest) = case el of
      Token t -> (off, Green.tokenKind t, Green.text t) : flatten (off + byteLength (Green.text t)) rest
      Node n -> flatten off (Green.children n) ++ flatten (off + fromIntegral (Green.length el)) rest

byteLength :: Text -> Int
byteLength = B.length . TE.encodeUtf8

------------------------------------------------------------------------
-- Renaming one identifier

-- | A name written exactly, possibly quoted.
renameExact :: Ctx -> Text -> Maybe Text
renameExact ctx v
  | identValue v /= cOld ctx = Nothing
  | "'" `T.isPrefixOf` v && T.length v >= 2 = Just ("'" <> cNew ctx <> "'")
  | otherwise = Just (cNew ctx)

-- | A quoted element is a terminal unless it is exactly a root.
renameQuoted :: Ctx -> Text -> Maybe Text
renameQuoted ctx v
  | identValue v == cOld ctx = Just ("'" <> cNew ctx <> "'")
  | otherwise = Nothing

-- | An index variable in a bound, possibly with @-1@.
renameIndex :: Ctx -> Text -> Maybe Text
renameIndex ctx v =
  let (base, offset) = case T.stripSuffix "-1" v of
        Just b -> (b, "-1")
        Nothing -> (v, "")
   in if base == cOld ctx then Just (cNew ctx <> offset) else Nothing

-- | A metavariable of a term: a root and a suffix, or @:name:text@.
renameTermMetavar :: Ctx -> Text -> Either Text (Maybe Text)
renameTermMetavar ctx v = case T.stripPrefix ":" v of
  Just rest ->
    let (name, after) = T.breakOn ":" rest
     in Right (if name == cOld ctx then Just (":" <> cNew ctx <> after) else Nothing)
  Nothing -> renameLexed ctx (Just False) v

-- | An identifier read by Ott's identifier lexer as a root and a suffix.
-- The kind, when given, selects nonterminals (True) or metavariables.
renameLexed :: Ctx -> Maybe Bool -> Text -> Either Text (Maybe Text)
renameLexed ctx kind v
  | Just v' <- renameIndex ctx v = Right (Just v')
  | otherwise = renameLexed' ctx kind v

renameLexed' :: Ctx -> Maybe Bool -> Text -> Either Text (Maybe Text)
renameLexed' ctx kind v =
  let lexes = filter wanted (lexIdent (cRoots ctx) v)
      wanted l = case (kind, l) of
        (Just True, TokNonterm _ _) -> True
        (Just False, TokMetavar _ _) -> True
        (Nothing, _) -> True
        _ -> False
      involved = filter involves lexes
   in case (lexes, involved) of
        (_, []) -> Right Nothing
        ([l], _)
          | render l == v -> Right (Just (render (renameTok l)))
          | otherwise -> Left ("cannot rename inside " <> quote v)
        _ -> Left (quote v <> " reads as more than one root and suffix, so it cannot be renamed safely")
  where
    old = cOld ctx
    rn x = if x == old then cNew ctx else x
    involves l = case l of
      TokMetavar r suff -> r == old || any mentionsSi suff
      TokNonterm r suff -> r == old || any mentionsSi suff
    mentionsSi si = case si of
      SiVar x _ -> x == old
      SiIndexed x inner -> x == old || mentionsSi inner
      _ -> False
    renameTok l = case l of
      TokMetavar r suff -> TokMetavar (rn r) (map renameSi suff)
      TokNonterm r suff -> TokNonterm (rn r) (map renameSi suff)
    renameSi si = case si of
      SiVar x o -> SiVar (rn x) o
      SiIndexed x inner -> SiIndexed (rn x) (renameSi inner)
      _ -> si
    render l = case l of
      TokMetavar r suff -> r <> T.concat (map renderSi suff)
      TokNonterm r suff -> r <> T.concat (map renderSi suff)
    renderSi si = case si of
      SiNum s -> s
      SiPunct s -> s
      SiVar x 0 -> x
      SiVar x (-1) -> x <> "-1"
      SiVar x o -> x <> T.pack (show o)
      SiIndexed x inner -> x <> renderSi inner
      SiIndex i -> "[" <> T.pack (show i) <> "]"
      SiIndexShift i k -> "[" <> T.pack (show i) <> "]" <> T.pack (show k)

------------------------------------------------------------------------
-- Applying edits

applyEdits :: Text -> [Edit] -> Text
applyEdits src es = TE.decodeUtf8 (B.concat (go 0 (sortOn editStart es)))
  where
    bs = TE.encodeUtf8 src
    go pos edits = case edits of
      [] -> [B.drop pos bs]
      e : rest -> B.take (editStart e - pos) (B.drop pos bs) : TE.encodeUtf8 (editNew e) : go (editEnd e) rest

------------------------------------------------------------------------
-- Checking the result

-- | The renamed files must load and check, and give the same grammar and
-- the same parses as the original up to the renaming.
verify :: Text -> Text -> Spec -> TermParser -> [(FilePath, Text)] -> [(FilePath, Text)] -> [(FilePath, Text)] -> Either [Problem] ()
verify old new spec tp oldDocs newSpecFiles newDocs = do
  loaded' <- either (Left . pure . loadProblem ("renaming " <> quote old <> " to " <> quote new <> " would make the specification fail to check here: ")) Right (loadSpec newSpecFiles)
  let spec' = ldSpec loaded'
      tp' = makeTermParser spec'
      rn x = if x == old then new else x
      before = specSignature rn spec ++ termSignature rn spec tp ++ docSignature rn tp oldDocs
      after = specSignature id spec' ++ termSignature id spec' tp' ++ docSignature id tp' newDocs
  case firstDifference before after of
    Nothing -> Right ()
    Just (a, b) ->
      Left
        [ Problem Nothing $
            "renaming " <> quote old <> " to " <> quote new <> " would change the meaning of the specification:\n  before: " <> clip a <> "\n  after:  " <> clip b
        ]

clip :: Text -> Text
clip t = if T.length t > 240 then T.take 240 t <> " ..." else t

firstDifference :: [Text] -> [Text] -> Maybe (Text, Text)
firstDifference as bs = case (as, bs) of
  ([], []) -> Nothing
  (a : as', b : bs')
    | a == b -> firstDifference as' bs'
    | otherwise -> Just (a, b)
  (a : _, []) -> Just (a, "(nothing)")
  ([], b : _) -> Just ("(nothing)", b)

tshow :: Show a => a -> Text
tshow = T.pack . show

-- | The grammar, without positions, with the roots renamed.
specSignature :: (Text -> Text) -> Spec -> [Text]
specSignature rn spec =
  [ "metavar " <> rn (mvdName md) <> " " <> tshow [(rn n, homs hs) | (n, hs) <- mvdNames md] <> " " <> homs (mvdHoms md) <> " " <> tshow (mvdIndexvar md)
  | md <- specMetavars spec
  ]
    ++ concat
      [ ("rule " <> rn (ruleName r) <> " " <> tshow [(rn n, homs hs) | (n, hs) <- ruleNames r] <> " " <> rulePrefix r <> " " <> homs (ruleHoms r) <> " " <> tshow (ruleMeta r, ruleSemiMeta r, rulePhantom r, ruleJudgement r))
          : [ "  prod " <> renameProdName rn (prodName p) <> " " <> tshow (prodMeta p, prodSugar p, Set.toList (prodCategories p)) <> " " <> tshow (map (renameElement rn) (prodElements p)) <> " " <> homs (prodHoms p) <> " " <> tshow (prodDisambiguate p) <> " " <> T.intercalate "; " (map (bindspec rn) (prodBindspecs p))
            | p <- ruleProds r
            ]
      | r <- specRules spec
      ]
    ++ ["subrule " <> rn (srLower s) <> " " <> rn (srUpper s) <> " " <> rn (srTop s) <> " " <> homs (srHoms s) | s <- specSubrules spec]
    ++ ["contextrule " <> rn (crNtr c) <> " " <> rn (crTarget c) <> " " <> rn (crHole c) | c <- specContextrules spec]
    ++ ["substitution " <> sbName s <> " " <> rn (sbThis s) <> " " <> rootRef (sbThat s) <> " " <> tshow (sbMultiple s) <> " " <> homs (sbHoms s) | s <- specSubstitutions spec]
    ++ ["freevar " <> fvName f <> " " <> rn (fvThis f) <> " " <> rootRef (fvThat f) <> " " <> homs (fvHoms f) | f <- specFreevars spec]
    ++ ["parsing " <> paLeft p <> " " <> paOperator p <> " " <> paRight p | p <- specParsing spec]
    ++ ["indexvar " <> rn v | v <- specIndexvars spec]
    ++ ["auxfn " <> f <> " " <> rn n | (f, n) <- specAuxfns spec]
    ++ ["embed " <> embedName e <> " " <> tshow [s | EmbedString s <- embedSpec e] | e <- specEmbeds spec]
    ++ concat
      [ ("defns " <> rn (dcName dc) <> " " <> dcWrapper dc <> " " <> homs (dcHoms dc))
          : [ "  defn " <> dName d <> " " <> dWrapper d <> " " <> tshow (map (renameElement rn) (dElements d)) <> " " <> tshow (dCategories d) <> " " <> homs (dHoms d)
            | d <- dcDefns dc
            ]
      | dc <- specDefnClasses spec
      ]
    ++ concat
      [ ("funs " <> fcName fc <> " " <> homs (fcHoms fc))
          : [ "  fun " <> fdName fd <> " " <> rn (fdResult fd) <> " " <> tshow (map (renameElement rn) (fdElements fd)) <> " " <> homs (fdHoms fd)
            | fd <- fcDefns fc
            ]
      | fc <- specFunClasses spec
      ]
  where
    -- references that resolve are positions; the others are terminals,
    -- target text that rename leaves as written
    homs hs = tshow hs
    rootRef r = case r of
      Mvr t -> "mvr " <> rn t
      Ntr t -> "ntr " <> rn t

bindspec :: (Text -> Text) -> Bindspec -> Text
bindspec rn b = case b of
  Bind m (r, s) _ -> "bind " <> mse rn m <> " in " <> rn r <> tshow (map (renameSuffixItem rn) s)
  AuxFnDef f m _ -> f <> " = " <> mse rn m
  NamesEqual m m' _ -> "names " <> mse rn m <> " = " <> mse rn m'
  NamesDistinct m m' _ -> "names " <> mse rn m <> " # " <> mse rn m'
  AllNamesDistinct m _ -> "distinctnames " <> mse rn m

mse :: (Text -> Text) -> Mse -> Text
mse rn m = case m of
  MetaVarExp v -> "mv " <> var v
  NonTermExp v -> "nt " <> var v
  MetaVarListExp v bd -> "mvlist " <> var v <> " " <> tshow (renameBound rn bd)
  NonTermListExp v bd -> "ntlist " <> var v <> " " <> tshow (renameBound rn bd)
  Aux f v -> "aux " <> f <> " " <> var v
  AuxList f v bd -> "auxlist " <> f <> " " <> var v <> " " <> tshow (renameBound rn bd)
  Union a b -> "(" <> mse rn a <> " union " <> mse rn b <> ")"
  Empty -> "{}"
  where
    var (r, s) = rn r <> tshow (map (renameSuffixItem rn) s)

renameElement :: (Text -> Text) -> Element -> Element
renameElement rn e = case e of
  Nonterm p r s -> Nonterm (rn p) (rn r) (map (renameSuffixItem rn) s)
  Metavar p r s -> Metavar (rn p) (rn r) (map (renameSuffixItem rn) s)
  Terminal t -> Terminal t
  ListForm lb -> ListForm lb {lbBound = fmap (renameBound rn) (lbBound lb), lbElements = map (renameElement rn) (lbElements lb)}

renameSuffixItem :: (Text -> Text) -> SuffixItem -> SuffixItem
renameSuffixItem rn si = case si of
  SiVar v o -> SiVar (rn v) o
  SiIndexed v inner -> SiIndexed (rn v) (renameSuffixItem rn inner)
  _ -> si

renameBound :: (Text -> Text) -> Bound -> Bound
renameBound rn b = case b of
  BoundDotform l u n -> BoundDotform (renameSuffixItem rn l) (renameSuffixItem rn u) n
  BoundComp v -> BoundComp (rn v)
  BoundCompU v u -> BoundCompU (rn v) (renameSuffixItem rn u)
  BoundCompLU v l u n -> BoundCompLU (rn v) (renameSuffixItem rn l) (renameSuffixItem rn u) n

-- | Ott names the productions of the synthesised @user_syntax@ rule after
-- the roots they embed.
renameProdName :: (Text -> Text) -> Text -> Text
renameProdName rn pn = case T.stripPrefix "user_syntax__" pn of
  Just r -> "user_syntax__" <> rn r
  Nothing -> pn

renameSymterm :: (Text -> Text) -> Symterm -> Symterm
renameSymterm rn st = case st of
  StNode ntr pn es -> StNode (rn ntr) (renameProdName rn pn) (map ste es)
  StNonterm ntr (r, s) -> StNonterm (rn ntr) (rn r, suff s)
  StNontermSub l t (r, s) -> StNontermSub (rn l) (rn t) (rn r, suff s)
  StUninterpreted s -> StUninterpreted s
  where
    suff = map (renameSuffixItem rn)
    ste e = case e of
      SteSt x -> SteSt (renameSymterm rn x)
      SteMetavar m (r, s) -> SteMetavar (rn m) (rn r, suff s)
      SteVar m v -> SteVar (rn m) v
      SteList ls -> SteList (map stli ls)
    stli l = case l of
      StliSingle es -> StliSingle (map ste es)
      StliListform b es -> StliListform (renameBound rn b) (map ste es)

-- | Every parse of every term of the specification, in order.
termSignature :: (Text -> Text) -> Spec -> TermParser -> [Text]
termSignature rn spec tp =
  [ trRoot r <> ": " <> parses (trRoot r) (trText r)
  | r <- termRequests spec
  ]
    ++ ["embed quotation: " <> parses "user_syntax" q | e <- specEmbeds spec, EmbedInner q <- embedSpec e]
  where
    parses root q = case parseTerms tp root False q of
      [] -> "no parses"
      ps -> T.intercalate " | " (map (ppPlainSymterm . renameSymterm rn) ps)

-- | Every parse of every quotation of the documents.
docSignature :: (Text -> Text) -> TermParser -> [(FilePath, Text)] -> [Text]
docSignature rn tp docs =
  [ T.pack f <> ": " <> parses written
  | (f, src) <- docs
  , Right qs <- [documentQuotations src]
  , (_, written, _) <- qs
  ]
  where
    parses q = case userSyntaxTransform (parseComplete tp "user_syntax" False q) of
      [] -> "no parses"
      ps -> T.intercalate " | " (map (ppPlainSymterm . renameSymterm rn . parseTerm) ps)

------------------------------------------------------------------------
-- Looking roots up, for editors

-- | A specification loaded once for looking its roots up: its files with
-- their terms spliced, and the documents filtered against it. It is
-- loaded with recovery, so it exists as long as the early checks find a
-- specification; while there are errors the terms are parsed with what
-- the checker kept of the grammar, and a line with no parse there (for
-- want of a production an error dropped, say) is left as a line, whose
-- roots are not found.
data Index = Index
  { ixRoots :: Roots
  , ixRenameable :: [Text]
  , ixParser :: TermParser
  , ixOwners :: M.Map Text (Set.Set Text)
  , ixSources :: [(Source, GreenNode Kind)]
  , ixDocs :: [(FilePath, Text)]
  }

indexSpec :: [(FilePath, Text)] -> [(FilePath, Text)] -> Maybe Index
indexSpec specFiles docFiles = do
  let checked = loadSpecRecovering specFiles
      sources = ckSources checked
  spec <- ckSpec checked
  let tp = makeTermParser spec
      splice s = let (t, _, _) = spliceTerms (FirstIfSame []) tp (srcTree s) in t
  pure
    Index
      { ixRoots = specRoots spec
      , ixRenameable = renameableRoots spec
      , ixParser = tp
      , ixOwners = M.unions (map (namedOwners . srcTree) sources)
      , ixSources = [(s, splice s) | s <- sources]
      , ixDocs = docFiles
      }

-- | The names 'renameRoot' accepts.
indexRenameable :: Index -> [Text]
indexRenameable = ixRenameable

-- | The roots of the specification, for its identifier lexer.
indexRoots :: Index -> Roots
indexRoots = ixRoots

-- | The tree of one of the specification's files, with its terms spliced.
indexTree :: Index -> FilePath -> Maybe (GreenNode Kind)
indexTree ix file = lookup file [(srcPath s, t) | (s, t) <- ixSources ix]

-- | Every place a root occurs, as the bytes of the identifiers that
-- 'renameRoot' would rewrite, in each file and document that has one.
occurrences :: Index -> Text -> [(FilePath, Text, [(Int, Int)])]
occurrences ix root =
  filter
    (\(_, _, rs) -> not (null rs))
    ( [(srcPath s, srcText s, ranges (treeEdits ctx s t)) | (s, t) <- ixSources ix]
        ++ [(f, src, ranges (docEdits ctx f src)) | (f, src) <- ixDocs ix]
    )
  where
    ctx = Ctx root root (ixRoots ix) (ixParser ix) (ixOwners ix)
    ranges (_, es) = [(editStart e, editEnd e) | e <- es]

-- | Where a root is declared: the names of metavariable declarations and
-- grammar rules.
declarations :: Index -> Text -> [(FilePath, Text, (Int, Int))]
declarations ix root =
  [ (srcPath s, srcText s, (fromIntegral (Range.start r), fromIntegral (Range.end r)))
  | (s, t) <- ixSources ix
  , c <- Cursor.descendants (Cursor.fromGreen (Node t))
  , Token tok <- [Cursor.green c]
  , Green.tokenKind tok == K.Ident
  , identValue (Green.text tok) == root
  , fmap Cursor.kind (Cursor.parent c) == Just K.Name
  , fmap Cursor.kind (Cursor.parent c >>= Cursor.parent) `elem` [Just K.MetavarDecl, Just K.Rule]
  , let r = Cursor.range c
  ]

-- | The root of the identifier at a byte offset of a file or document, if
-- the identifier is one of its occurrences: the root itself when the
-- identifier reads as a root with a suffix, before an index variable of
-- the suffix.
rootAt :: Index -> FilePath -> Int -> Maybe Text
rootAt ix file off = case lookup file texts of
  Nothing -> Nothing
  Just src ->
    let ws = [w | (o, w) <- identWords src, o <= off, off <= o + byteLength w]
        candidates = nub (concatMap rootsOf ws)
        covers (a, b) = a <= off && off <= b
        occursHere r = or [any covers rs | (f, _, rs) <- occurrences ix r, f == file]
     in case filter occursHere candidates of
          r : _ -> Just r
          [] -> Nothing
  where
    texts = [(srcPath s, srcText s) | (s, _) <- ixSources ix] ++ ixDocs ix
    rootsOf w =
      [identValue w | identValue w `elem` allRoots]
        ++ concat [tokRoots l | l <- lexIdent (ixRoots ix) w]
    allRoots = rootsNonindexMetavars (ixRoots ix) ++ rootsIndexvars (ixRoots ix) ++ rootsNonterms (ixRoots ix)
    tokRoots l = case l of
      TokMetavar r suff -> r : concatMap siRoots suff
      TokNonterm r suff -> r : concatMap siRoots suff
    siRoots si = case si of
      SiVar x _ -> [x]
      SiIndexed x inner -> x : siRoots inner
      _ -> []
