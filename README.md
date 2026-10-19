# haskott

A Haskell reimplementation of [Ott](https://github.com/ott-lang/ott), the tool
for writing semantic definitions of programming languages (Sewell et al.,
"Ott: Effective tool support for the working semanticist", JFP 20(1), 2010).

It takes the Ott input syntax exactly as the
[andreabedini/ott](https://github.com/andreabedini/ott) fork accepts it
(including its Typst backend, quoted terminals and nested dot forms), checks a
definition as Ott does, and writes what Ott writes: TeX and Typst output, the
`[[ ... ]]` document filters, and the definitions for Coq, Isabelle, HOL,
Lem, OCaml and Twelf. The driving use is the formalisation of the Haskell
2010 revised report in the `formalisation` directory of
`haskell-2010-revised-report`.

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
- Milestone 6, Typst output: `Haskott.Tex` in its Typst dialect, the
  fork's Typst dialect of Ott's TeX back end, from the runtime of defaults
  through the metavariable and grammar tables, the symbolic terms of rules
  with Ott's spacing, homs, suffixes, dot forms and comprehensions, the
  definition and function blocks, the `[[ ]]` document filter and the
  final counts. On the report (`ott/style.ott` with `expressions.ott` and
  with `layout.ott`, plus the filtered `report.src.typ`) the output is
  byte for byte the fork's, and `make OTT=haskott` builds the report's
  PDFs. The differential also compares the Typst output of every corpus
  file.
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
- Milestone 8, error recovery: `parseDocumentRecovering` goes on after a
  parse error from the next line where an item, rule, production,
  definition or function can start; what it skipped becomes an
  `ErrorItem` node, so the tree still renders to the file.
  `checkDocumentRecovering` records an error and drops only the
  production, rule, declaration, definition or global check it is about.
  The first error of both is Ott's, so the Ott-compatible paths still
  stop there. `haskott check` (through `Haskott.Diagnostics`) reports
  every problem of a file; the rule lines are checked once the grammar
  has no errors, since otherwise most of their problems would be
  consequences. `cabal test recovery` breaks the first productions of
  every corpus file one at a time and checks that each costs only its own
  line, and the corpus suite checks the first problem of every file
  against `test/first-diagnostics.tsv`.
- Milestone 9, language server: `haskott lsp` speaks the Language Server
  Protocol over stdio. A specification can span several files, so they
  are listed in a `haskott.json`, in the order Ott reads them, with the
  documents filtered against each. For a file, the nearest `haskott.json`
  at or above its directory (up to the workspace root) counts, and its
  paths are relative to its own directory:

  ```json
  { "specs": [ { "files": ["ott/style.ott", "ott/expressions.ott"], "picky": true,
                 "documents": ["doc/report.src.typ"] },
               { "files": ["ott/style.ott", "ott/layout.ott"], "picky": true } ] }
  ```

  A file none lists is a specification of its own. Open files are read
  from the editor, the others from disk.
  - Diagnostics: every problem (`Haskott.Diagnostics`) of the
    specifications an edited file is part of, a short while after the last
    change; a newer change cancels a check still running. A file in
    several specifications shows the problems of all of them.
  - Navigation: go to the declaration of a metavariable, index variable or
    grammar rule; find its references and highlight them, in the files and
    documents of the specification (the occurrences `rename` would edit);
    and an outline of each file (`Haskott.Outline`).
  - Rename: the verified `haskott rename`, applied to every specification
    the edit reaches, so a file shared by two specifications is renamed in
    both. The edit names the versions of the open files it was computed
    from, so an editor refuses it if a file changed meanwhile.
  - Semantic tokens: every token classified (`Haskott.Highlight`), so
    that an editor with no grammar of Ott can highlight from them alone.
    What the grammar makes of each identifier comes from the term parse
    for rule lines, clauses and quotations, and from Ott's identifier
    lexer for the elements of productions and forms, comprehension
    bounds, binding specifications, hom references and the roots of
    subrules, substitutions and the like: terminals as keywords
    (alphanumeric) or operators, nonterminals as variables, metavariables
    as parameters, index variables as type parameters, `lex` variables as
    strings. The other names by their place: productions as enum members,
    judgements and functions as functions, rule names as methods,
    categories as modifiers, prefixes and groups as namespaces, with
    `declaration` on the roots a declaration names. Keywords, punctuation
    and comments as such, hom names as macros, hom bodies as strings and
    `com` homs as documentation comments. While the specification has
    errors, rule lines are parsed with what the checker kept of the
    grammar, so a broken production elsewhere leaves the other lines
    classified.

  `cabal test lsp` drives the server through a client.
- Milestone 10, TeX output: `Haskott.Tex` in its LaTeX dialect, Ott's
  TeX back end, with the preamble of default commands, `tex-preamble`,
  `tex-wrap-pre` and `tex-wrap-post` embeds, and `-tex_filter`. As in
  Ott, the two dialects share the structure of the output and differ in
  its leaves, and the term parses of a LaTeX target must print the same
  to be taken without `-picky_multiple_parses`. The differential
  compares the TeX output of every corpus file, byte for byte; it also
  agrees on the report's specifications and filtered document.
- Milestone 11, prover output: the definitions for Coq (`.v`), Isabelle
  (`.thy`), HOL (`Script.sml`), Lem (`.lem`), OCaml (`.ml`) and Twelf
  (`.twf`, where Ott fails on what it does not implement), as ports
  of Ott's printers under `Haskott.Prover`: the types of the grammar
  grouped by their dependencies, the inductive relations of the
  definitions, functions, subrule predicates, auxiliary functions,
  substitutions, free variables, context application, Coq induction
  principles, Coq's locally nameless representation and its expanded
  list types (`-coq_expand_list_types true`), the entries in source
  order between Ott's preamble and postamble, and the prover document
  filters (`-coq_filter` and the like). The checks Ott makes only for a
  prover target come first: the homs of meta productions, the order of
  rule groups, the types of auxiliary functions. Ott's printers are
  impure and its definitions come in the order ocamlgraph visits them,
  which depends on a vertex counter every graph of the run shares;
  `Haskott.Graph` models the ocamlgraph operations Ott uses, and the
  printers run in a state monad with Ott's counters, effects in the
  order OCaml evaluates them. The differential compares the output of
  each target on every corpus file with `ott -o` (`--target` chooses):
  all agree byte for byte, as they do under each of Ott's prover
  options and on the tapl example's Makefile run.
- Also: `-merge true`, merging the rules, definition classes,
  definitions and functions of the same name across files (the TeX and
  prover outputs of the tapl example agree with Ott's); Ott's stop at a
  rule with no or several conclusions; its check of the bounds of every
  rule before TeX output; and `-output_source_locations` in every
  output, the lines of each construct worked out from the tree as
  Ott's parser reports them (`Haskott.SourceLoc`; the differential's
  `--source-locations N`).
- Not yet done: the OCaml lexer and parser generators (`.mll`, `.mly`,
  `-ocaml_pp`), `-writesys`/`-readsys`, and Ott's debugging outputs.

haskott takes Ott's command line for the implemented part: `haskott -i
FILE... -o OUT.tex|OUT.typ|OUT.v|OUT.thy|OUTScript.sml|OUT.lem|OUT.ml|OUT.twf
[-tex_filter SRC DST] [-typst_filter SRC DST] [-coq_filter SRC DST]
[-isa_filter SRC DST] [-hol_filter SRC DST] [-lem_filter SRC DST]
[-ocaml_filter SRC DST] [-picky_multiple_parses BOOL] [-merge BOOL]
[-output_source_locations N]
[-coq_avoid N] [-coq_expand_list_types BOOL] [-coq_names_in_rules BOOL]
[-coq_use_filter_fn BOOL] [-coq_lngen BOOL] [-isabelle_primrec BOOL]
[-isabelle_inductive BOOL] [-isa_syntax BOOL] [-isa_generate_lemmas BOOL]
[-ocaml_include_terminals BOOL] [-no_rbcatn BOOL]
[-tex_name_prefix P] [-tex_show_meta BOOL] [-tex_show_categories BOOL]
[-tex_colour BOOL] [-tex_wrap BOOL] [-tex_suppress_category C]
[-tex_suppress_ntr N]`. The development subcommands look at one stage
each: `cabal run haskott -- check FILE...` runs the whole pipeline on
files and reports every problem with its line and column (`--picky` makes
several parses of a term an error); `roots` lists the names `rename`
accepts; `dump` prints the tree after stage one
and `dump --terms` after the term splice, `showraw` the raw specification
as Ott prints it, `spec` the checked specification, `structure` the
entries of the prover output in order, and `parse FILE ':root: text'`
every parse of a term in Ott's plain form.

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
[ott](https://github.com/andreabedini/ott) (the `typst` work) and the
report's formalisation, at `../ott` and
`../haskell-2010-revised-report/formalisation` by default; `HASKOTT_OTT` and
`HASKOTT_REPORT_OTT` name them when they are elsewhere. What Ott does with
each file is recorded in `test/ott-acceptance.tsv`, regenerated by
`scripts/ott-acceptance.zsh` from the Ott binary in the ott checkout, so the
suite itself needs no Ott.

## Reference material

`ott-jfp.pdf` in this directory is the paper; it is not tracked.
