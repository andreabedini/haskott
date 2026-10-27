# haskott

A Haskell reimplementation of [Ott](https://github.com/ott-lang/ott), the
tool for writing semantic definitions of programming languages (Sewell et
al., "Ott: Effective tool support for the working semanticist", JFP 20(1),
2010).

haskott reads `.ott` files, checks them as Ott does, and writes what Ott
writes: TeX, the `[[ ... ]]` document filters, and the definitions for
Coq, Isabelle, HOL, Lem, OCaml and Twelf. On Ott's own `tests/` and
`examples/` its output is Ott's, byte for byte. It takes Ott's command
line, so it can stand in for `ott` in a Makefile.

The input language is Ott 0.34's, with four extensions of haskott's own:
Typst output, with `typst` homs and embeds and a `-typst_filter`; quoted
terminals in productions (`'in'`, `'::'`), which Ott reads as ordinary
identifiers and haskott as terminals; nested dot forms; and shifted
indices (`e_n-1`). Ott rejects a `typst` hom and the last two as bad
rules. `GRAMMAR.md` specifies the source language.

Unlike Ott, haskott parses a specification into a lossless concrete syntax
tree (a [graft](https://github.com/andreabedini/graft) green tree:
whitespace and comments are tokens in the tree) and derives everything else
from it. That is what makes `haskott rename` and the language server
possible: a specification can be edited without disturbing the text the
edit is not about.

The driving use is the formalisation of the Haskell 2010 revised report, in
the `formalisation` directory of `haskell-2010-revised-report`.

## Building

haskott depends on a sibling checkout of graft; `cabal.project` fixes the
layout:

```
<parent>/haskott   (this repository)
<parent>/graft     (a checkout of andreabedini/graft)
```

With GHC 9.12.2 and cabal (from ghcup):

```console
$ cabal build all
$ cabal run haskott -- check test/extensions/lambda.ott
test/extensions/lambda.ott: ok
```

## Using it as Ott

```
haskott -i FILE... -o OUT [-tex_filter SRC DST] [-typst_filter SRC DST]
        [-coq_filter SRC DST] [-isa_filter SRC DST] [-hol_filter SRC DST]
        [-lem_filter SRC DST] [-ocaml_filter SRC DST]
        [-picky_multiple_parses BOOL] [-merge BOOL] [-output_source_locations N]
        [-coq_avoid N] [-coq_expand_list_types BOOL] [-coq_names_in_rules BOOL]
        [-coq_use_filter_fn BOOL] [-coq_lngen BOOL]
        [-isabelle_primrec BOOL] [-isabelle_inductive BOOL] [-isa_syntax BOOL]
        [-isa_generate_lemmas BOOL] [-ocaml_include_terminals BOOL] [-no_rbcatn BOOL]
        [-tex_name_prefix P] [-tex_show_meta BOOL] [-tex_show_categories BOOL]
        [-tex_colour BOOL] [-tex_wrap BOOL] [-tex_suppress_category C]
        [-tex_suppress_ntr N]
```

The output format follows the extension of `-o`: `.tex`, `.typ`, `.v`
(Coq), `.thy` (Isabelle), `.sml` (HOL), `.lem`, `.ml` (OCaml), `.twf`
(Twelf). Several `-i` and `-o` may be given; as in Ott, an output takes the
inputs since the previous output of its target. An argument ending in
`.ott` is an input without `-i`. For example, the report builds its
grammar tables with

```console
$ haskott -i ott/style.ott -i ott/expressions.ott -o build/expressions.typ
```

and `make OTT=haskott` in its `formalisation` directory builds the PDFs.

Behaviour copied from Ott, including its less obvious parts: `-merge true`
merges rules, definition classes, definitions and functions of the same
name across files; a rule with no or several conclusions stops the run; the
bounds of every rule are checked before TeX output; a term with several
parses is an error only under `-picky_multiple_parses true`, otherwise the
first parse is used when every requested target prints them the same (TeX
and the provers but OCaml; never Typst); `-output_source_locations N`
annotates every output with the source lines Ott's parser would report.

Not implemented: the OCaml lexer and parser generators (`.mll`, `.mly`,
`-ocaml_pp`, `-ocaml_pp_ast_module`, `-ocaml_pp_json`),
`-writesys`/`-readsys`, `-twelf_filter`, `-generate_aux_rules`,
`-quotient_rules`, `-aux_style_rules`, `-lift_cons_prefixes`,
`-signal_parse_errors`, `-fast_parse`, `-sort`, `-process_defns`, `-alltt`,
`-colour`, and Ott's debugging outputs (`-showraw`, `-show_sort`,
`-show_defns`, `-pp_grammar`, `-dot`, `-ugly`). An option haskott does not
know is an error, not a warning.

## Checking a specification

```
haskott check [--picky] FILE...
```

runs the whole pipeline on the files of one specification and reports every
problem with its line and column, where Ott stops at the first. Parsing
recovers at the next line where an item, rule, production, definition or
function can start; checking drops only the construct an error is about.
The rule lines of the definitions are checked once the grammar has no
errors, since with a broken grammar most of their problems would be
consequences. The first problem reported is the one Ott reports. `--picky`
makes several parses of a term an error.

## Renaming

```
haskott rename [--write] OLD NEW FILE...
```

renames a metavariable, index variable or grammar-rule root across the
`.ott` files of a specification (in the order Ott reads them) and the
`[[ ]]` quotations of the documents filtered against it (the other files
given). It edits every identifier Ott reads as that root with any suffix,
or as a root whose suffix mentions the index variable: in declarations,
productions, judgement forms, bounds, bindspecs, hom references that
resolve to an element, subrules, context rules, substitutions, free
variables, function results, the parsed rule lines and the quotations.
Comments, hom bodies and other text stay as written; mentions of the root
found there are listed as notes.

Every rename is verified before anything is written: the renamed files are
loaded, checked and parsed again and must give the same grammar and the
same parse of every term, up to the renaming. A rename to an existing root,
a terminal, a keyword, or a name that changes how anything lexes is refused
with the reason. Without `--write` the edits are only listed. `haskott
roots FILE...` lists the names `rename` accepts.

## Language server

```
haskott lsp
```

speaks the Language Server Protocol over stdio (a trailing `--stdio`, as
editors add it, is accepted).

A specification can span several files, and one file can be part of
several specifications, so they are listed in a `haskott.json`. For a file,
the nearest `haskott.json` at or above its directory, up to the workspace
root, counts; its paths are relative to its own directory. `files` lists a
specification's files in the order Ott reads them; `picky` (default false)
is `-picky_multiple_parses`; `documents` (default none) are the documents
filtered against it, whose quotations a rename rewrites too. The report's:

```json
{ "specs": [ { "files": ["ott/style.ott", "ott/expressions.ott"], "picky": true,
               "documents": ["doc/report.src.typ"] },
             { "files": ["ott/style.ott", "ott/layout.ott"], "picky": true } ] }
```

A file no specification lists is a specification of its own. Open files are
read from the editor, the others from disk.

The server provides diagnostics (every problem of each specification an
edited file is part of, a short while after the last change; a newer change
cancels a check still running); go to declaration, find references and
document highlights for metavariables, index variables and grammar rules
across the files and documents of a specification; an outline of each
file; rename, with the verification of `haskott rename`, applied to every
specification the edit reaches, so a file shared by two specifications is
renamed in both (the edit carries the versions of the open files it was
computed from, so an editor refuses it if a file changed meanwhile); and
semantic tokens, so an editor with no grammar of Ott can highlight from
them alone. Terminals, nonterminals, metavariables and index variables in
rule lines are classified from the term parse, so the highlighting shows
what the grammar makes of each identifier; while the specification has
errors elsewhere, the lines are parsed with what the checker kept of the
grammar.

## Development subcommands

Each looks at one stage of the pipeline:

| command | shows |
|---|---|
| `haskott dump FILE` | the lossless tree after parsing |
| `haskott dump --terms FILE` | the tree after the rule lines are parsed into terms |
| `haskott showraw FILE` | the raw specification, as `ott -showraw` prints it |
| `haskott spec FILE` | the checked specification |
| `haskott structure FILE...` | the entries of the prover output, in order |
| `haskott parse FILE ':root: text'` | every parse of a term, as `ott -parse` prints them |
| `haskott roots FILE...` | the names `rename` accepts |

## How it agrees with Ott

The acceptance corpus is the 116 `tests/` and 38 `examples/` files of Ott
0.34: 154 files, of which Ott parses 150 and accepts 119.
`test/ott-acceptance.tsv` records what Ott does with each (`accepted`,
`other-error`, `parse-error`); `scripts/ott-acceptance.zsh` regenerates it
from `bin/ott` in the Ott checkout.

`cabal test` runs five suites, none of which runs Ott:

- `corpus`: haskott parses exactly the files Ott parses; every parsed file
  renders back byte for byte, before and after the rule lines are parsed
  into terms; the first problem `haskott check` reports for each file is
  the one in `test/first-diagnostics.tsv`.
- `recovery`: every corpus file parses with recovery into a tree that
  renders back to the input, and breaking one production costs exactly
  that production.
- `rename-sweep`: every root of every accepted file (and of the report with
  its document) is renamed to a fresh name and back, and the files come
  back byte for byte.
- `extensions`: the small specifications in `test/extensions/`, one per
  extension, are accepted and give the TeX and Typst output recorded
  beside them, and the report's specifications check clean. No Ott can
  check these.
- `lsp`: drives the server through a client.

The suites read Ott's `tests/` and `examples/` from a checkout of Ott 0.34
at `../ott`, and the report from
`../haskell-2010-revised-report/formalisation`; `HASKOTT_OTT` and
`HASKOTT_REPORT_OTT` name them when they are elsewhere.

`cabal run haskott-differential` needs `bin/ott` built in that checkout.
For every file Ott parses it compares, in turn: the raw parse with
`ott -showraw`; the checked specification with `ott -show_sort` (whether
the file checks and, per production, each element's text and class and the
homs); every parse of every premise, conclusion, formula, quotation and
function clause with `ott -parse`; and the TeX and each prover's output,
byte for byte, with Ott's default options. `--target` (coq, isa, hol, lem,
ocaml, twf) and `--only SUBSTRING` narrow the run; `--source-locations N`
passes `-output_source_locations N` to both. All 150 files agree.

## Design

The pipeline is a sequence of projections of one tree. `Haskott.Syntax`
parses a file into the lossless tree (`GRAMMAR.md` is its specification);
`Haskott.Raw` projects it into the counterpart of Ott's raw parse;
`Haskott.Spec.Check` follows Ott's `check_and_disambiguate`;
`Haskott.Term.Grammar` and `Haskott.Term.Earley` build and run the
character-level term parser as Ott's `new_term_parser.ml` does;
`Haskott.Term.Splice` replaces every rule line, clause and quotation that
parses by the term's subtree, so the whole file is one tree down to the
leaves of its terms and still renders byte for byte; `Haskott.Tex` (in a
LaTeX and a Typst dialect) and `Haskott.Prover` print it. `Haskott.Rename`,
`Haskott.Diagnostics`, `Haskott.Outline` and `Haskott.Highlight` work on
the same tree. Each module's header explains how it matches Ott and where
it does not.

## Reference material

Sewell, Zappa Nardelli, Owens, Peskine, Ridge, Sarkar and Strniša, "Ott:
Effective tool support for the working semanticist", Journal of Functional
Programming 20(1), 2010. Ott's manual is in the `doc/` directory of its
repository.
