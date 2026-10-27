-- | haskott: a Haskell reimplementation of Ott.
--
-- The pipeline is a sequence of projections of one lossless tree, and this
-- is the map of it. Each module's header says how it matches Ott and where
-- it does not.
--
-- * "Haskott.Syntax" parses a file into the lossless tree (a graft green
--   tree; @GRAMMAR.md@ is its specification and "Haskott.Syntax.Parser"
--   implements it, "Haskott.Syntax.Kind" names its tokens and nodes, and
--   "Haskott.Syntax.Ast" gives typed views of them).
-- * "Haskott.Raw" projects the tree into the counterpart of Ott's raw parse;
--   "Haskott.Raw.Show" prints it as @ott -showraw@ does.
-- * "Haskott.Spec.Check" follows Ott's @check_and_disambiguate@ into the
--   checked specification of "Haskott.Spec" (with "Haskott.Spec.Suffix" for
--   Ott's suffix lexing); "Haskott.Spec.Show" prints it as @ott -show_sort@
--   does.
-- * "Haskott.Term.Grammar" and "Haskott.Term.Earley" build and run the
--   character-level term parser as Ott's @new_term_parser.ml@ does;
--   "Haskott.Term.Parse" and "Haskott.Term.Requests" drive it,
--   "Haskott.Term.Symterm" is the term representation, "Haskott.Term.Merge"
--   the dot-form merging, and "Haskott.Term.Splice" replaces every rule
--   line, clause and quotation that parses by the term's subtree, so the
--   whole file is one tree down to the leaves of its terms and still renders
--   byte for byte ("Haskott.Term.Tree").
-- * "Haskott.Defns" processes the definitions as Ott's @defns.ml@ does.
-- * "Haskott.Tex" prints TeX and, in its Typst dialect, Typst, and runs the
--   document filters; "Haskott.Prover" and its submodules print the prover
--   targets, with "Haskott.Graph" standing in for ocamlgraph so definition
--   order follows Ott's; "Haskott.SourceLoc" supplies
--   @-output_source_locations@.
-- * "Haskott.Load" loads a specification from several files; on top of it,
--   "Haskott.Diagnostics" reports every problem with recovery,
--   "Haskott.Rename" renames a root, "Haskott.Outline" and
--   "Haskott.Highlight" serve the language server, and "Haskott.Project"
--   reads @haskott.json@.
module Haskott
  ( module Haskott.Syntax
  ) where

import Haskott.Syntax
