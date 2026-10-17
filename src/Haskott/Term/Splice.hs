{-# LANGUAGE OverloadedStrings #-}

-- | Stage two of the parse: the rule lines of the lossless tree are
-- parsed as symbolic terms and replaced by their subtrees.
--
-- The premises and conclusions of rules, the clauses of functions and the
-- quotations of comment blocks among the rules are parsed with the
-- grammar-derived term parser; each 'Line' token (or quotation) that
-- parses is replaced by the term's elements, so that the tree still
-- renders to the source byte for byte. A premise's trailing @[[:name]]@
-- becomes a 'PremiseName' node, and a premise of embedded prover code an
-- 'EmbedPremise' node whose quotations are terms. A line with no parse,
-- or with several that the policy does not resolve, is left as it was; the diagnostics for
-- those come from "Haskott.Defns", which parses the same lines (through
-- the cache this splice returns). Lines of lineless blocks, which Ott joins
-- into one term, are left as lines.
module Haskott.Term.Splice
  ( spliceTerms
  ) where

import Control.Monad.Trans.State.Strict (State, gets, modify, runState)
import qualified Data.Map.Strict as M
import Data.Text (Text)
import qualified Data.Text as T
import Graft
import qualified Graft.Cursor as Cursor
import qualified Graft.Green as Green
import Haskott.Spec (Diagnostic (..))
import Haskott.Syntax.Ast (defnName, defnsWrapper, funsName)
import Haskott.Syntax.Kind (Kind (..))
import Haskott.Term.Parse
import Haskott.Term.Requests (embeddedQuotations, ruleNameParse)
import Haskott.Term.Tree (termElements)

type C = Cursor Kind

type S = State (ParseCache, [Diagnostic])

-- | Replace the rule lines of the document by term subtrees. Returns the
-- new tree, the parser with every parse made cached, and the quotations
-- of comment blocks that did not parse (Ott parses those only when it
-- produces output, so they are warnings rather than errors).
spliceTerms :: ParsePolicy -> TermParser -> GreenNode Kind -> (GreenNode Kind, TermParser, [Diagnostic])
spliceTerms policy tp doc =
  let c = Cursor.fromGreen (Node doc)
      (els, (cache, diags)) = runState (concat <$> mapM top (Cursor.children c)) (M.empty, [])
   in (Green.node (Green.nodeKind doc) els, withCache cache tp, reverse diags)
  where
    keep c = pure [Cursor.green c]

    rebuild :: C -> (C -> S [GreenElement Kind]) -> S [GreenElement Kind]
    rebuild c f = do
      els <- concat <$> mapM f (Cursor.children c)
      pure [Node (Green.node (Cursor.kind c) els)]

    top c = case Cursor.kind c of
      Defns -> rebuild c (defnsChild (maybe "" defnsWrapper (castNode c)))
      Funs -> rebuild c (funsChild (maybe "" funsName (castNode c)))
      _ -> keep c

    defnsChild wrapper c = case Cursor.kind c of
      Defn -> rebuild c (defnChild (wrapper <> maybe "" defnName (castNode c)))
      _ -> keep c

    defnChild prodName c = case Cursor.kind c of
      DRule -> rebuild c (druleChild prodName)
      DefnCom -> rebuild c defnComChild
      _ -> keep c

    druleChild prodName c = case Cursor.kind c of
      Premise -> rebuild c premiseChild
      Conclusion -> rebuild c (lineChild "formula" (defnTransform prodName))
      _ -> keep c

    funsChild name c = case Cursor.kind c of
      Fundefn -> rebuild c (fundefnChild name)
      _ -> keep c

    fundefnChild name c = case Cursor.kind c of
      Clause -> rebuild c (lineChild name userSyntaxTransform)
      _ -> keep c

    -- a conclusion or clause: the line, then its trailing whitespace
    lineChild root transform c = case Cursor.kind c of
      Line -> do
        let (body, trailing) = splitTrailing (tokenTextOf c)
        parsed <- parseLine root transform body
        pure (case parsed of
          Just els -> els ++ spaceToken trailing
          Nothing -> [Cursor.green c])
      _ -> keep c

    -- a premise: the term, then an optional [[:name]], then whitespace;
    -- or embedded prover code with quoted terms
    premiseChild c = case Cursor.kind c of
      Line -> do
        let (body, trailing) = splitTrailing (tokenTextOf c)
            (body', label) = ruleNameParse body
            (term, gap) = splitTrailing body'
            labelEls = case label of
              Just l -> [Node (Green.node PremiseName [Token (Green.token RefOpen "[["), Token (Green.token PremiseLabel (":" <> l)), Token (Green.token RefClose "]]")])]
              Nothing -> []
            -- ruleNameParse keeps the text before the label as is
            after = spaceToken gap ++ labelEls ++ spaceToken trailing
        parsed <- case embeddedQuotations term of
          Just _ -> embedded term
          Nothing -> parseLine "formula" userSyntaxTransform term
        pure (case parsed of
          Just els -> els ++ after
          Nothing -> [Cursor.green c])
      _ -> keep c

    -- {{ text [[ term ]] text }}: every quotation must parse for the
    -- premise to be spliced
    embedded s = do
      let inner = maybe s id (T.stripPrefix "{{" s >>= T.stripSuffix "}}")
      parts <- quotationParts inner
      pure $ case parts of
        Nothing -> Nothing
        Just els -> Just [Node (Green.node EmbedPremise ([Token (Green.token HomOpen "{{")] ++ els ++ [Token (Green.token HomClose "}}")]))]

    quotationParts t = case T.breakOn "[[" t of
      (before, rest)
        | T.null rest -> pure (Just (homTextTokens before))
        | otherwise -> do
            let (q, after) = T.breakOn "]]" (T.drop 2 rest)
            parsed <- parseLine "user_syntax" userSyntaxTransform q
            case parsed of
              Nothing -> pure Nothing
              Just els -> do
                more <- quotationParts (T.drop 2 after)
                pure $ case more of
                  Nothing -> Nothing
                  Just els' -> Just (homTextTokens before ++ [Node (Green.node HomRef ([Token (Green.token RefOpen "[[")] ++ quoted q els ++ [Token (Green.token RefClose "]]")]))] ++ els')

    -- a quotation's term with the whitespace around it
    quoted q els =
      let (lead, _) = T.span isBlank q
          (_, trailing) = splitTrailing q
       in spaceToken lead ++ els ++ spaceToken trailing

    -- a comment block's [[ ]] quotations are terms of user syntax
    defnComChild c = case Cursor.kind c of
      HomRef -> do
        let inner = [i | i <- Cursor.children c, Cursor.kind i /= RefOpen, Cursor.kind i /= RefClose]
            q = T.concat (map (Green.render . Cursor.green) inner)
        parsed <- parseLine "user_syntax" userSyntaxTransform q
        case parsed of
          Just els -> pure [Node (Green.node HomRef ([Token (Green.token RefOpen "[[")] ++ quoted q els ++ [Token (Green.token RefClose "]]")]))]
          Nothing -> do
            modify (\(cache, ds) -> (cache, Diagnostic (Cursor.range c) ("quotation \"" <> T.strip q <> "\" does not parse as user syntax") : ds))
            keep c
      _ -> keep c

    -- the elements of a term, if it has exactly one parse (or, when not
    -- picky, at least one); leading whitespace of the text stays in front
    parseLine :: Text -> Transform -> Text -> S (Maybe [GreenElement Kind])
    parseLine root transform s = do
      let key = (root, stripTrailingWhitespace s)
      cache <- gets fst
      let parses = case M.lookup key cache of
            Just ps -> ps
            Nothing -> parseComplete tp root False s
      modify (\(ca, ds) -> (M.insert key parses ca, ds))
      pure $ case selectParse policy (transform parses) of
        Just p -> Just (termElements (termGrammar tp) (snd key) (parseTree p))
        Nothing -> Nothing

    tokenTextOf c = case Cursor.green c of
      Token t -> Green.text t
      Node nd -> Green.renderNode nd

    isBlank ch = ch `elem` (" \t\f\r\n" :: String)
    splitTrailing s = let body = T.dropWhileEnd isBlank s in (body, T.drop (T.length body) s)
    spaceToken s = [Token (Green.token Space s) | not (T.null s)]

    homTextTokens :: Text -> [GreenElement Kind]
    homTextTokens s
      | T.null s = []
      | isBlank (T.head s) = let (b, rest) = T.span isBlank s in Token (Green.token Space b) : homTextTokens rest
      | otherwise = let (w, rest) = T.break isBlank s in Token (Green.token HomText w) : homTextTokens rest
