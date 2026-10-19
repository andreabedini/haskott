-- | What the tokens of a specification are, for an editor's highlighting.
--
-- Every token of a file's tree is classified, so that an editor with no
-- grammar of Ott of its own can highlight from this alone; one that has
-- one (tree-sitter-ott) gets from it what its grammar cannot know, what
-- the grammar of the file makes of an identifier:
--
-- * the terms of rule lines, function clauses and quotations, from the
--   tree after the term splice ("Haskott.Term.Splice"), whose tokens the
--   term parser has classified;
-- * the elements of productions and of judgement and function forms, and
--   the bounds of their comprehensions, with Ott's identifier lexer as the
--   checker reads them (an element with no parse is a terminal, a quoted
--   one is a terminal unless it is exactly a root, and one with several
--   parses is an error and left out);
-- * the roots named by declarations, @[[ ]]@ references in homs, binding
--   specifications, subrules, context rules, substitutions, free
--   variables and function results.
--
-- The other identifiers are classified by their place in the construct,
-- as "Haskott.Syntax.Ast" reads them: production, definition, rule and
-- function names, categories, prefixes. A rule line that is not spliced,
-- because it does not parse, is left out, and so is text skipped after a
-- parse error.
module Haskott.Highlight
  ( Class (..)
  , Highlight (..)
  , highlights
  ) where

import Data.Char (isAlphaNum, isDigit)
import Data.Maybe (listToMaybe, mapMaybe)
import Data.Text (Text)
import qualified Data.Text as T
import Graft
import qualified Graft.Cursor as Cursor
import qualified Graft.Green as Green
import qualified Graft.Range as Range
import Haskott.Spec.Suffix (IdentTok (..), Roots (..), lexIdent)
import Haskott.Syntax.Ast (identValue)
import Haskott.Syntax.Kind (Kind (..), isTrivia)

data Class
  = -- * Identifiers the grammar of the file decides
    Terminal
    -- ^ a terminal whose spelling starts with a letter or digit
  | Operator
    -- ^ any other terminal
  | Nonterminal
  | Metavariable
  | IndexVariable
  | Variable
    -- ^ a concrete variable, admitted by a @lex@ hom
  | Pseudo
    -- ^ a @:prodname:@ or @:concrete:@ pseudo-terminal
  | Number
  | ListSyntax
    -- ^ dots and the delimiters of comprehensions
  | Label
    -- ^ the name of a premise, @[[:name]]@
    -- * Names by their place
  | Production
    -- ^ a production name
  | Definition
    -- ^ the name of a judgement, function, substitution or free-variable
    -- function, or of an auxiliary function in a binding specification
  | RuleName
    -- ^ the name of an inference rule
  | Category
    -- ^ a category of a production, judgement or rule (@M@, @S@, ...)
  | Group
    -- ^ a prefix, the name of a group of definitions or functions, or of
    -- a Coq section
    -- * The metalanguage
  | MetaKeyword
  | Punctuation
  | Comment
  | Documentation
    -- ^ the text of a @com@ hom or comment block
  | HomName
  | HomBody
    -- ^ the text of any other hom or embed, for its back end
  deriving (Eq, Ord, Show)

data Highlight = Highlight
  { hlStart :: Int
  , hlEnd :: Int
  -- ^ bytes
  , hlClass :: Class
  , hlDeclaration :: Bool
  -- ^ whether the token declares the root it names
  }
  deriving (Eq, Show)

type C = Cursor Kind

-- | The classified tokens of a file's tree, in order.
highlights :: Roots -> GreenNode Kind -> [Highlight]
highlights roots tree =
  [ Highlight (fromIntegral (Range.start r)) (fromIntegral (Range.end r)) cls decl
  | c <- Cursor.descendants (Cursor.fromGreen (Node tree))
  , Token t <- [Cursor.green c]
  , Just (cls, decl) <- [classify roots c (Green.tokenKind t) (Green.text t)]
  , let r = Cursor.range c
  , Range.end r > Range.start r
  ]

classify :: Roots -> C -> Kind -> Text -> Maybe (Class, Bool)
classify roots c k s = case k of
  TTerminal -> use (terminal s)
  TNonterm -> use Nonterminal
  TMetavar -> use Metavariable
  TVar -> use Variable
  TProdName -> use Pseudo
  TIndex -> use IndexVariable
  TNumber -> use Number
  PremiseLabel -> use Label
  LineComment -> use Comment
  BlockComment -> use Comment
  Keyword -> use MetaKeyword
  _ | isTrivia k -> Nothing
  _ | k `elem` [Dots, CompOpen, CompMiddle, CompClose, CompIn] -> case homText of
        Just cls -> use cls
        Nothing -> use ListSyntax
  _ | k `elem` punctuation -> use Punctuation
  Dashes -> use Punctuation
  HomText -> case above of
    CompBound : _ -> fmap plain (bound s)
    HomRef : rest | Hom `elem` rest -> fmap plain (lexed s)
    HomRef : _ -> Nothing
    _ | isHomName -> use HomName
    _ -> fmap plain homText
  _ -> case above of
    CompBound : _ -> fmap plain (bound s)
    _ -> case k of
      Element -> fmap plain (element s)
      QuotedElement -> fmap plain (quoted s)
      Ident -> ident
      _ -> Nothing
  where
    use cls = Just (cls, False)
    plain cls = (cls, False)
    above = map Cursor.kind (ancestors c)
    parentKind = listToMaybe above

    -- the text of a hom, embed or comment block, outside its quotations
    homText
      | HomRef `elem` above = Nothing
      | otherwise = case [b | b <- ancestors c, Cursor.kind b `elem` [Hom, Embed, DefnCom]] of
          b : _
            | Cursor.kind b == DefnCom || homNameOf b == Just (T.pack "com") -> Just Documentation
            | otherwise -> Just HomBody
          [] -> Nothing
    isHomName = case Cursor.parent c of
      Just p | Cursor.kind p `elem` [Hom, Embed, DefnCom] -> fmap Cursor.range (firstHomText p) == Just (Cursor.range c)
      _ -> False

    -- an identifier of the metalanguage, by the node it is in and the
    -- segment of that node, between its @::@ tokens, it is in
    ident = case parentKind of
      Just Name -> case drop 1 above of
        MetavarDecl : _ -> case Cursor.parent c >>= Cursor.parent of
          Just d | isIndexvarDecl d -> declared IndexVariable
          _ -> declared Metavariable
        Rule : _ -> declared Nonterminal
        _ -> root
      Just Rule -> use Group
      Just Prod -> segmented [Nothing, Just Category, Just Production]
      Just Defns -> use Group
      Just Defn -> segmented [Nothing, Just Category, Just Definition, Just Group]
      Just RuleLine -> segmented [Just Category, Just RuleName]
      Just Funs -> use Group
      Just Fundefn -> case segmentOf c of
        1 -> root
        _ -> use Definition
      Just Substitution -> segmented' root (use Definition)
      Just Freevar -> segmented' root (use Definition)
      Just Subrule -> root
      Just Contextrule -> root
      Just ParsingAnnotation -> use Production
      Just HomsSection -> use Group
      Just HomsItem -> use Production
      Just CoqSection -> use Group
      Just CoqVariable -> use Group
      Just Mse
        | nextIs LParen -> use Definition
        | otherwise -> root
      Just Bindspec -> root
      _ -> Nothing
      where
        declared cls = Just (cls, True)
        root = fmap plain (lexed (identValue s))
        segmented classes = case drop (segmentOf c) classes of
          Just cls : _ -> use cls
          _ -> Nothing
        segmented' before after = if segmentOf c == 0 then before else after
        nextIs kind = fmap Cursor.kind (listToMaybe (dropWhile (isTrivia . Cursor.kind) (followingSiblings c))) == Just kind

    terminal t = case T.uncons t of
      Just (ch, _) | isAlphaNum ch -> Terminal
      _ -> Operator

    lexed t = case lexIdent roots t of
      [TokMetavar m []] | m `elem` rootsIndexvars roots -> Just IndexVariable
      [TokMetavar _ _] -> Just Metavariable
      [TokNonterm _ _] -> Just Nonterminal
      _ -> Nothing

    element t = case lexIdent roots t of
      [] -> Just (terminal t)
      _ -> lexed t

    -- a quoted element is a terminal unless its content is exactly a root
    quoted t =
      let inner = T.drop 1 (T.dropEnd 1 t)
       in case lexIdent roots inner of
            [TokMetavar _ []] -> lexed inner
            [TokNonterm _ []] -> lexed inner
            _ -> Just (terminal inner)

    bound t
      | not (T.null t) && T.all isDigit t = Just Number
      | t `elem` rootsIndexvars roots || maybe False (`elem` rootsIndexvars roots) (T.stripSuffix (T.pack "-1") t) = Just IndexVariable
      | otherwise = Nothing

punctuation :: [Kind]
punctuation =
  [ Comma, ColonColonEq, Bar, ColonColon, LtColonColon, UnderscoreColonColon, LtEq
  , HomOpen, HomClose, BindOpen, BindClose, Eq, Hash, LParen, RParen, Empty
  , RefOpen, RefClose
  ]

ancestors :: C -> [C]
ancestors c = maybe [] (\p -> p : ancestors p) (Cursor.parent c)

followingSiblings :: C -> [C]
followingSiblings c = case Cursor.parent c of
  Nothing -> []
  Just p -> drop 1 (dropWhile (\s -> Cursor.range s /= Cursor.range c || Cursor.kind s /= Cursor.kind c) (Cursor.children p))

-- | How many @::@ tokens come before a token among its siblings.
segmentOf :: C -> Int
segmentOf c = case Cursor.parent c of
  Nothing -> 0
  Just p ->
    length
      [ s
      | s <- Cursor.children p
      , Cursor.kind s == ColonColon
      , Range.end (Cursor.range s) <= Range.start (Cursor.range c)
      ]

firstHomText :: C -> Maybe C
firstHomText p = listToMaybe [s | s <- Cursor.children p, Cursor.kind s == HomText]

homNameOf :: C -> Maybe Text
homNameOf p = case fmap Cursor.green (firstHomText p) of
  Just (Token t) -> Just (Green.text t)
  _ -> Nothing

isIndexvarDecl :: C -> Bool
isIndexvarDecl d =
  T.pack "indexvar"
    `elem` mapMaybe
      (\s -> case Cursor.green s of
        Token t | Green.tokenKind t == Keyword -> Just (Green.text t)
        _ -> Nothing)
      (Cursor.children d)
