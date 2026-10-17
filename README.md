# haskott

A Haskell reimplementation of [Ott](https://github.com/ott-lang/ott), the tool
for writing semantic definitions of programming languages (Sewell et al.,
"Ott: Effective tool support for the working semanticist", JFP 20(1), 2010).

The first target is the half of Ott that checks a definition and typesets it:
the Ott input syntax exactly as the
[andreabedini/ott](https://github.com/andreabedini/ott) fork accepts it
(including its Typst backend, quoted terminals and nested dot forms), Typst and
TeX output, and the `[[ ... ]]` document filter. Proof-assistant backends come
later. The driving use is the formalisation of the Haskell 2010 revised report
in `haskell-report-ott`.

Unlike Ott, haskott parses a specification into a lossless concrete syntax tree
(a [graft](../graft) green tree, rowan's model: whitespace and comments are
tokens in the tree) and derives everything else from it, so a specification
can be renamed, reformatted and edited without disturbing the text the edit is
not about.

## Status

- Milestone 1, the specification of the Ott source language: `GRAMMAR.md`.
- Milestone 2, the stage-one parser: `Haskott.Syntax.parseDocument` turns an
  Ott source file into a lossless green tree. On the acceptance corpus
  (Ott's 125 `tests/` and 33 `examples/` files plus the report's
  `expressions.ott`) it accepts exactly the files Ott 0.34 accepts and
  renders every accepted file back byte for byte (`cabal test`).
- Milestone 3a, the raw specification: `Haskott.Syntax.Ast` gives typed
  views over the tree and `Haskott.Raw` projects them into plain data, the
  counterpart of Ott's raw parse. `cabal run haskott-differential` prints
  it in the format of `ott -showraw` and compares with Ott on every corpus
  file; all 155 agree byte for byte.
- Milestone 3b, the checked specification: `Haskott.Spec.Check` follows
  Ott's `check_and_disambiguate`: it synthesises the judgement, formula and
  user-syntax grammars from the definitions, merges hom sections, resolves
  roots and synonyms, classifies every element of every production with
  Ott's identifier lexer (root plus suffix), merges dot forms into list
  forms, resolves `[[ ]]` references in homs to element positions, converts
  binding specifications, and performs Ott's checks on all of that (with
  the exceptions listed in the module header). The differential also
  compares it with `ott -show_sort`: on all 155 corpus files the two agree
  on whether the file checks and, for every production, on each element's
  text and class and on the homs.
- Milestone 4, the term parser: `Haskott.Term.Grammar` builds the
  character-level grammar of symbolic terms from the checked specification
  exactly as Ott's `new_term_parser.ml` does (whitespace, suffixes, index
  variables, concrete variables, list forms with dot forms and
  comprehensions, `:prodname:` and `:concrete:` pseudo-terminals, follow
  restrictions, reject and transparent productions, priorities), and
  `Haskott.Term.Earley` parses with it: an Earley recogniser followed by
  derivation enumeration under the same rejects and Visser-style priority
  checks. `Haskott.Defns` processes the definitions as Ott's `defns.ml`
  does. The differential runs `ott -parse` on every premise, conclusion,
  formula, quotation and function clause of every corpus file: all parse
  to the same sets of symbolic terms, and the two tools accept the same
  files.
- Milestone 5, the spliced tree: `Haskott.Term.Splice` replaces every
  premise, conclusion, function clause and comment-block quotation that
  parses by the term's lossless subtree (`Haskott.Term.Tree`: production
  nodes named by rule and production, list nodes, and tokens for
  terminals, nonterminals, metavariables, variables, pseudo-terminals and
  bound items, with the whitespace between them), so the whole file is one
  tree from the document down to the leaves of its terms and still renders
  byte for byte. The corpus suite checks that round trip on every file
  that checks. Lines that do not parse stay lines; a term with several
  parses is spliced with the first unless `--picky`.
- Milestone 6, Typst output: `Haskott.Typst` is the fork's Typst dialect of
  Ott's TeX back end, from the runtime of defaults through the metavariable
  and grammar tables, the symbolic terms of rules with Ott's spacing,
  homs, suffixes, dot forms and comprehensions, the definition and
  function blocks, the `[[ ]]` document filter and the final counts. On
  the report (`ott/style.ott` with `expressions.ott` and with
  `layout.ott`, plus the filtered `report.src.typ`) the output is byte for
  byte the fork's, and `make OTT=haskott` builds the report's PDFs. The
  differential also compares the Typst output of every corpus file.
- Milestone 7, rename: `haskott rename [--write] OLD NEW FILE...` renames
  a metavariable, index variable or grammar-rule name across the `.ott`
  files of a specification and the `[[ ]]` quotations of documents
  filtered against it (the other files given). It edits the identifiers
  Ott reads as that root, with any suffix, or as a root whose suffix
  mentions the index variable: in declarations, productions and
  judgement forms, bounds, bindspecs, hom references that resolve to an
  element, subrules, context rules, substitutions, free variables,
  function results, the parsed rule lines and the quotations. Comments,
  hom bodies and other target text stay as written, and the mentions of
  the root found there are listed as notes. Every rename is checked
  before anything is written: the renamed files are loaded, checked and
  parsed again, and must give the same grammar and the same parse of
  every term, up to the renaming. Renames to an existing root, a
  terminal, a keyword, or a name that changes how anything lexes are
  refused with the reason. Without `--write` the edits are only listed.
  `cabal test rename-sweep` renames every root of every corpus file (and
  of the report with its document) to a fresh name and back, and
  checks that the files come back byte for byte.
- Not yet done: TeX output, Ott's remaining checks (bounds consistency at
  output time among them), prover back ends, error-tolerant parsing, a
  language server.

haskott takes Ott's command line for the implemented part: `haskott -i
FILE... -o OUT.typ [-typst_filter SRC DST] [-picky_multiple_parses BOOL]
[-tex_name_prefix P] [-tex_show_meta BOOL] [-tex_show_categories BOOL]
[-tex_colour BOOL] [-tex_wrap BOOL] [-tex_suppress_category C]
[-tex_suppress_ntr N]`. The development subcommands look at one stage
each: `cabal run haskott -- check FILE...` runs the whole pipeline on
files and reports every problem with its line and column (`--picky` makes
several parses of a term an error); `roots` lists the names `rename`
accepts; `dump` prints the tree after stage one
and `dump --terms` after the term splice, `showraw` the raw specification
as Ott prints it, `spec` the checked specification, and `parse FILE
':root: text'` every parse of a term in Ott's plain form.

## Building and testing

haskott depends on a sibling checkout of graft. The layout is fixed:

```
<parent>/haskott   (this repository)
<parent>/graft     (a checkout of andreabedini/graft)
```

Toolchain: GHC 9.12.2 and cabal from ghcup.

```console
$ cabal build all
$ cabal test
```

The test suite reads the acceptance corpus from checkouts of
[ott](https://github.com/andreabedini/ott) (the `typst` work) and
haskell-report-ott, next to this repository by default; `HASKOTT_OTT` and
`HASKOTT_REPORT_OTT` name them when they are elsewhere. What Ott does with
each file is recorded in `test/ott-acceptance.tsv`, regenerated by
`scripts/ott-acceptance.zsh` from the Ott binary in the ott checkout, so the
suite itself needs no Ott.

## Reference material

`ott-jfp.pdf` in this directory is the paper; it is not tracked.
