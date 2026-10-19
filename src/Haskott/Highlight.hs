-- | What the tokens of a specification are, for an editor's highlighting.
--
-- The metalanguage has the same structure in every file, and an editor can
-- highlight it with a grammar of its own (tree-sitter-ott). What such a
-- grammar cannot know is what the grammar of the file makes of an
-- identifier: whether an element of a production or a word of a rule line
-- is a terminal, a nonterminal, a metavariable or an index variable. This
-- module answers that, for:
--
-- * the terms of rule lines, function clauses and quotations, from the
--   tree after the term splice ("Haskott.Term.Splice"), whose tokens the
--   term parser has classified;
-- * the elements of productions and of judgement and function forms, and
--   the bounds of their comprehensions, with Ott's identifier lexer as the
--   checker reads them (an element with no parse is a terminal, a quoted
--   one is a terminal unless it is exactly a root, and one with several
--   parses is an error and left out);
-- * the identifiers of @[[ ]]@ references in homs and of binding
--   specifications, which name elements, when they lex as a root.
--
-- Declarations, keywords, comments and hom bodies are left to the
-- editor's grammar. A rule line that is not spliced, because it does not
-- parse or because the specification has errors, is left out.
module Haskott.Highlight
  ( Class (..)
  , highlights
  ) where

import Data.Char (isAlphaNum, isDigit)
import qualified Data.Text as T
import Graft
import qualified Graft.Cursor as Cursor
import qualified Graft.Green as Green
import qualified Graft.Range as Range
import Haskott.Spec.Suffix (IdentTok (..), Roots (..), lexIdent)
import Haskott.Syntax.Ast (identValue)
import Haskott.Syntax.Kind (Kind (..))

data Class
  = Terminal
    -- ^ a terminal whose spelling starts with a letter or digit
  | Operator
    -- ^ any other terminal
  | Nonterminal
  | Metavariable
  | IndexVariable
  | Variable
    -- ^ a concrete variable, admitted by a @lex@ hom
  | ProdName
    -- ^ a @:prodname:@ or @:concrete:@ pseudo-terminal
  | Number
  | ListSyntax
    -- ^ dots and the delimiters of comprehensions
  | Label
    -- ^ the name of a premise, @[[:name]]@
  deriving (Eq, Ord, Show)

-- | The classified tokens of a file's tree, as byte ranges in order.
highlights :: Roots -> GreenNode Kind -> [(Int, Int, Class)]
highlights roots tree =
  [ (fromIntegral (Range.start r), fromIntegral (Range.end r), cls)
  | c <- Cursor.descendants (Cursor.fromGreen (Node tree))
  , Token t <- [Cursor.green c]
  , Just cls <- [classify (map Cursor.kind (ancestors c)) (Green.tokenKind t) (Green.text t)]
  , let r = Cursor.range c
  , Range.end r > Range.start r
  ]
  where
    ancestors c = maybe [] (\p -> p : ancestors p) (Cursor.parent c)

    classify above k s = case k of
      TTerminal -> Just (terminal s)
      TNonterm -> Just Nonterminal
      TMetavar -> Just Metavariable
      TVar -> Just Variable
      TProdName -> Just ProdName
      TIndex -> Just IndexVariable
      TNumber -> Just Number
      PremiseLabel -> Just Label
      _ | k `elem` [Dots, CompOpen, CompMiddle, CompClose, CompIn] ->
            if inHomBody above then Nothing else Just ListSyntax
      _ -> case above of
        CompBound : _ -> bound s
        _ -> case k of
          Element -> element s
          QuotedElement -> quoted s
          HomText | HomRef `elem` take 1 above, Hom `elem` above -> reference s
          Ident | any (`elem` [Mse, Bindspec]) (take 1 above) -> reference (identValue s)
          _ -> Nothing

    -- the text of a hom, embed or comment block, outside its quotations
    inHomBody above = HomRef `notElem` above && any (`elem` [Hom, Embed, DefnCom]) above

    terminal s = case T.uncons s of
      Just (ch, _) | isAlphaNum ch -> Terminal
      _ -> Operator

    lexed s = case lexIdent roots s of
      [TokMetavar m []] | m `elem` rootsIndexvars roots -> Just IndexVariable
      [TokMetavar _ _] -> Just Metavariable
      [TokNonterm _ _] -> Just Nonterminal
      _ -> Nothing

    element s = case lexIdent roots s of
      [] -> Just (terminal s)
      _ -> lexed s

    -- a quoted element is a terminal unless its content is exactly a root
    quoted s =
      let inner = T.drop 1 (T.dropEnd 1 s)
       in case lexIdent roots inner of
            [TokMetavar _ []] -> lexed inner
            [TokNonterm _ []] -> lexed inner
            _ -> Just (terminal inner)

    reference = lexed

    bound s
      | not (T.null s) && T.all isDigit s = Just Number
      | s `elem` rootsIndexvars roots || maybe False (`elem` rootsIndexvars roots) (T.stripSuffix (T.pack "-1") s) = Just IndexVariable
      | otherwise = Nothing
