# haskott

A Haskell reimplementation of [Ott](https://github.com/ott-lang/ott), the
tool for writing semantic definitions of programming languages (Sewell et
al., "Ott: Effective tool support for the working semanticist", JFP 20(1),
2010).

haskott reads `.ott` files, checks them as Ott does, and writes what Ott
writes: TeX, the `[[ ... ]]` document filters, and the definitions for
Coq, Isabelle, HOL, Lem, OCaml and Twelf. On Ott's own `tests/` and
`examples/` its output is Ott's, byte for byte, and it takes Ott's command
line, so it can stand in for `ott` in a Makefile. Beyond Ott, it reports
every problem of a specification with its position where Ott stops at the
first, renames a name across a specification and the documents that quote
it, writes Typst as well as TeX, and runs as a language server for editors.

An Ott specification declares a grammar and defines judgements over it:

```
metavar x ::= {{ tex \mathit{[[x]]} }}            % a hom attaches output text
grammar
  t :: 't_' ::=
    | x          :: :: var
    | \ x . t    :: :: lam  (+ bind x in t +)     % a binding specification
    | t t'       :: :: app                        % t' is the root t with suffix '
defns J :: '' ::=
  defn t --> t' :: :: red :: '' by
    ------------------------- :: beta             % a rule: premises, line, conclusion
    (\ x . t) t' --> t' x t
```

Homs such as `{{ tex ... }}` carry text for one back end, with `[[ ]]`
quoting a term to be typeset; an identifier in a rule is a declared root
plus a suffix. [GRAMMAR.md](https://github.com/andreabedini/haskott/blob/main/GRAMMAR.md)
specifies the source language exactly, for implementers and for working
out why a file is rejected; to learn Ott, read
[its manual](http://www.cl.cam.ac.uk/~pes20/ott/top2.html).

Unlike Ott, haskott parses a specification into a lossless concrete syntax
tree (a [graft](https://github.com/andreabedini/graft) green tree:
whitespace and comments are tokens in the tree) and derives everything else
from it. That is what makes `haskott rename` and the language server
possible: a specification can be edited without disturbing the text the
edit is not about.

The driving use is the formalisation of the
[Haskell 2010 revised report](https://github.com/andreabedini/haskell-2010-revised-report),
in its `formalisation` directory. The section
[Differences from Ott](#differences-from-ott) says what haskott adds, what
it leaves out, and where it behaves differently.

## Install

### Pre-built binaries

Download the archive for your platform from the
[latest release](https://github.com/andreabedini/haskott/releases/latest)
and unpack it. It contains the `haskott` executable. There are archives for
x86_64 and aarch64 Linux, x86_64 and aarch64 macOS, and x86_64 Windows.

- Linux binaries need glibc 2.34 or newer (e.g. Ubuntu 22.04, Debian 12,
  RHEL 9), libgmp and zlib.
- macOS binaries are not notarised. Remove the quarantine attribute before
  running one: `xattr -d com.apple.quarantine haskott`.

Each release also has `SHA256SUMS`, and a GitHub attestation for every
file. To check an archive:

```
sha256sum --check --ignore-missing SHA256SUMS
gh attestation verify ARCHIVE --repo andreabedini/haskott
```

### With mise

[mise](https://mise.jdx.dev/) installs the release archive for your
platform with its
[GitHub backend](https://mise.jdx.dev/dev-tools/backends/github.html), and
checks its checksum and attestation:

```
mise use -g github:andreabedini/haskott
```

Add `@VERSION` to pin a version, for example
`github:andreabedini/haskott@0.1.0.0`. Without `-g`, the tool is added to
the current project's `mise.toml`.

### From source

```console
$ git clone https://github.com/andreabedini/haskott
$ cd haskott
$ cabal update
$ cabal build all
$ cabal run haskott -- check test/extensions/lambda.ott
test/extensions/lambda.ott: ok
```

haskott is built on [graft](https://github.com/andreabedini/graft), which
is not on Hackage yet: `cabal.project` pins a commit of its repository, and
cabal clones it. To build against a checkout of graft instead, name it in
`cabal.project.local`, as the comment in `cabal.project` shows. Each
release also has the source distribution `haskott-VERSION.tar.gz`, which
needs graft from Hackage, so for now build from the repository.

GHC 9.12.2 and 9.14.1 are the tested compilers; the bounds admit GHC 9.6
and later. To use haskott from a Makefile, put it on the path:

```console
$ cabal install exe:haskott
```

## Using it as Ott

```
haskott -i FILE... -o OUT... [OPTION]...
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

The options are Ott's, with Ott's defaults:

| option | |
|---|---|
| `-tex_filter SRC DST`, `-typst_filter SRC DST` | replace the `[[ ]]` quotations of a document |
| `-coq_filter`, `-isa_filter`, `-hol_filter`, `-lem_filter`, `-ocaml_filter SRC DST` | the same for a prover's text |
| `-picky_multiple_parses BOOL` | several parses of a term are an error (default false: the first is used when every requested target prints them the same, as Ott decides for TeX and the provers except OCaml, and never for Typst) |
| `-merge BOOL` | merge rules, definition classes, definitions and functions of the same name across files |
| `-output_source_locations N` | annotate the output with the source lines Ott's parser would report (0, 1 or 2) |
| `-signal_parse_errors BOOL` | exit 1 when a rule or clause fails to parse |
| `-coq_avoid N`, `-coq_expand_list_types`, `-coq_names_in_rules`, `-coq_use_filter_fn`, `-coq_lngen BOOL` | Coq output |
| `-isabelle_primrec`, `-isabelle_inductive`, `-isa_syntax`, `-isa_generate_lemmas BOOL` | Isabelle output |
| `-ocaml_include_terminals`, `-no_rbcatn BOOL` | OCaml and Lem output |
| `-tex_name_prefix P`, `-tex_show_meta`, `-tex_show_categories`, `-tex_colour`, `-tex_wrap BOOL`, `-tex_suppress_category C`, `-tex_suppress_ntr N` | TeX and Typst output |

Any other option is an error, not a warning; the list above is complete.
Behaviour copied from Ott, including its less obvious parts: a rule with no
or several conclusions stops the run; the bounds of every rule are checked
before TeX output; a rule or clause that does not parse is reported, the
output is still written, and the exit status is 0 unless
`-signal_parse_errors true`; every other error exits with status 2.

## Differences from Ott

**Extensions.** Four, all of haskott's own; the Ott checkout the tests use
is stock Ott 0.34, which has none of them.

- Typst output (`-o FILE.typ`, `-typst_filter`), with `typst` homs and
  embeds. Ott rejects a `typst` hom as illegal.
- Quoted terminals in productions (`'in'`, `'::'`). Ott dequotes an element
  and reads it like any other identifier, so `'in'` with a metavariable `i`
  and an index variable `n` is that metavariable; haskott reads a quoted
  element as a terminal unless its content is exactly a declared root
  ([GRAMMAR.md §3.4](https://github.com/andreabedini/haskott/blob/main/GRAMMAR.md#34-elements)).
- Nested dot forms (`K_1 p_1_1 .. p_1_k1 -> e_1 ; .. ; K_n p_n_1 .. p_n_kn -> e_n`)
  and shifted indices (`e_n-1` in a dot form), in TeX and Typst output only.
  Ott rejects both as rules that do not parse.

**Streams and status.** Ott writes everything to stdout; haskott writes
diagnostics and warnings to stderr, in `FILE:LINE:COL: message` form, and
only Ott's rule counts to stdout. Exit statuses are Ott's: 2 on an error,
1 for unparsed rules under `-signal_parse_errors true`, 0 otherwise. A
quotation in a filtered document that does not parse is typeset as written
and reported as a warning, as Ott reports it.

**Two intended divergences in parsing.** A file that is not valid UTF-8 is
rejected (Ott reads bytes). A last line consisting of one word with no
final newline is accepted (Ott rejects it through an off-by-one in its
lexer). Both are in GRAMMAR.md, with the corpus files they affect.

**Not implemented.** The OCaml lexer and parser generators (`.mll` and
`.mly` outputs, `-ocaml_pp`, `-ocaml_pp_ast_module`, `-ocaml_pp_json`);
`-writesys` and `-readsys`; `-generate_aux_rules`, `-quotient_rules` and
`-aux_style_rules`, which Ott has on by default, so the `aux`, `auxparam`,
`quotient-with` and `quotient-remove` homs are accepted and not acted on;
`-parse`, `-lem_debug`, `-fast_parse`, `-sort`, `-process_defns`, `-alltt`,
`-colour` and the debugging outputs (`-showraw`, `-show_sort`,
`-show_defns`, `-pp_grammar`, `-dot`, `-ugly`; `haskott showraw` and
`haskott spec` are the counterparts of the first two); `-i` files with an
output extension, which Ott copies into the output. Of Ott's checks, the
context-rule checks and the productivity check are not implemented. A
lineless rule (a block of lines with no dashed line, Ott's test-harness
form) is accepted and reported as a diagnostic.

## Checking a specification

```
haskott check [--picky] FILE...
```

reads the files as one specification, in Ott's order, and reports every
problem with its line and column, where Ott stops at the first. Parsing
recovers at the next construct and checking drops only the construct an
error is about; the rule lines are checked once the grammar has no errors.
The first problem reported is the one Ott reports. `--picky` makes several
parses of a term an error. The exit status is 1 when there are errors.
How recovery works is in the header of `Haskott.Diagnostics`.

## Renaming

```
haskott rename [--write] OLD NEW FILE...
```

renames a metavariable, index variable or grammar-rule root across the
`.ott` files of a specification (in the order Ott reads them) and the
documents filtered against it (the other files given), everywhere the name
is read as that root: declarations, productions, judgement forms,
bindspecs, hom references, rule lines, quotations. Comments and hom bodies
stay as written; mentions found there are listed as notes. Every rename is
verified before anything is written: the renamed files must give the same
grammar and the same parse of every term, up to the renaming, and a rename
that would capture a suffix, clash with a terminal, keyword or root, or
change how anything lexes is refused with the reason. Without `--write` the
edits are only listed. `haskott roots FILE...` lists the names `rename`
accepts. The header of `Haskott.Rename` has the full list of what is
edited.

## Language server

```
haskott lsp
```

speaks the Language Server Protocol over stdio (a trailing `--stdio`, as
editors add it, is accepted). [vscode-ott](https://github.com/andreabedini/vscode-ott)
is a client, and [tree-sitter-ott](https://github.com/andreabedini/tree-sitter-ott)
a grammar for the metalanguage that editors can pair with it.

### haskott.json

A specification can span several files, and one file can be part of
several specifications, so they are listed in a `haskott.json`. For a file,
the nearest `haskott.json` at or above its directory, up to the workspace
root, counts; its paths are relative to its own directory. A file no
specification lists is a specification of its own. The report's:

```json
{ "specs": [ { "files": ["ott/style.ott", "ott/expressions.ott"], "picky": true,
               "documents": ["doc/report.src.typ"] },
             { "files": ["ott/style.ott", "ott/layout.ott"], "picky": true } ] }
```

| key | |
|---|---|
| `files` | the specification's files, in the order Ott reads them (required) |
| `picky` | `-picky_multiple_parses` (default false) |
| `documents` | documents filtered against it, whose quotations rename rewrites too (default none) |

### What the server provides

- `textDocument/publishDiagnostics`: every problem of each specification an
  edited file is part of, a short while after the last change (a newer
  change cancels a check still running). Open files are read from the
  editor, the others from disk; sync is incremental.
- `textDocument/definition`, `references`, `documentHighlight`: for
  metavariables, index variables and grammar rules, across the files and
  documents of a specification.
- `textDocument/documentSymbol`: an outline of each file.
- `textDocument/prepareRename`, `rename`: with the verification of
  `haskott rename`, applied to every specification the edit reaches, so a
  file shared by two specifications is renamed in both. The edit carries
  the versions of the open files it was computed from, so an editor refuses
  it if a file changed meanwhile.
- `textDocument/semanticTokens/full`: see below.

No hover, completion, formatting or code actions.

### Semantic tokens

Terminals, nonterminals, metavariables and index variables in rule lines
are classified from the term parse, so the highlighting shows what the
grammar makes of each identifier; while the specification has errors
elsewhere, the lines are parsed with what the checker kept of the grammar.
The standard legend is used, with these meanings; `declaration` marks a
declaration and `documentation` the text of `com` homs.

| what | token type |
|---|---|
| terminal spelt with a letter or digit; metalanguage keyword | `keyword` |
| other terminal; punctuation; dots and comprehension delimiters | `operator` |
| nonterminal | `variable` |
| metavariable | `parameter` |
| index variable | `typeParameter` |
| concrete variable admitted by a `lex` hom; the body of a hom or embed | `string` |
| `:prodname:` and `:concrete:` pseudo-terminals; hom name | `macro` |
| number in a bound | `number` |
| premise name `[[:name]]` | `decorator` |
| production name | `enumMember` |
| judgement, function, substitution or free-variable function name | `function` |
| rule name | `method` |
| category (`M`, `S`, ...) | `modifier` |
| prefix, definitions group or Coq section name | `namespace` |
| comment; `com` hom text | `comment` |

## Development subcommands

`haskott help` lists every subcommand. Each of these looks at one stage of
the pipeline:

| command | shows |
|---|---|
| `haskott dump FILE` | the lossless tree after parsing |
| `haskott dump --terms FILE` | the tree after the rule lines are parsed into terms |
| `haskott showraw FILE` | the raw specification, as `ott -showraw` prints it |
| `haskott spec FILE` | the checked specification |
| `haskott structure FILE...` | the entries of the prover output, in order |
| `haskott parse FILE ':root: text'` | every parse of a term, as `ott -parse` prints them |
| `haskott roots FILE...` | the names `rename` accepts |

## Tests

The acceptance corpus is the 116 `tests/` and 38 `examples/` files of Ott
0.34: 154 files, of which Ott parses 150 and accepts 119.
`test/ott-acceptance.tsv` records what Ott does with each (`accepted`,
`other-error`, `parse-error`); `scripts/ott-acceptance.zsh` regenerates it
from `bin/ott` in the Ott checkout.

`cabal test` runs five suites, none of which runs Ott:

- `corpus`: haskott parses exactly the files Ott parses; every parsed file
  renders back byte for byte, before and after the rule lines are parsed
  into terms; the first problem `haskott check` reports for each file is
  the one in `test/first-diagnostics.tsv`; and the quirks of GRAMMAR.md §6,
  which the corpus does not exercise, behave as recorded in `inlineCases`.
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
`HASKOTT_REPORT_OTT` name them when they are elsewhere. CI runs the suites
on every platform of a release with a checkout of Ott 0.34 and without the
report, which the suites that use it then skip.

`cabal run haskott-differential` needs `bin/ott` built in that checkout.
For every file Ott parses it compares, in turn: the raw parse with
`ott -showraw`; the checked specification with `ott -show_sort` (whether
the file checks and, per production, each element's text and class and the
homs); every parse of every premise, conclusion, formula, quotation and
function clause with `ott -parse`; and the TeX and each prover's output,
byte for byte, with Ott's default options. `--target` (coq, isa, hol, lem,
ocaml, twf) and `--only SUBSTRING` narrow the run; `--source-locations N`
passes `-output_source_locations N` to both. All 150 files agree. Three
files whose ambiguous terms haskott orders differently from Ott have their
outputs skipped; the report is unaffected because it sets
`-picky_multiple_parses true`.

## Design

The pipeline is a sequence of projections of one lossless tree. The header
of the [`Haskott`](https://github.com/andreabedini/haskott/blob/main/src/Haskott.hs)
module maps the modules onto Ott's sources, and each module's header says
how it matches Ott and where it does not.

## Documentation

The API documentation of the latest release is at
<https://andreabedini.github.io/haskott/>. Each
[release](https://github.com/andreabedini/haskott/releases) also has the
documentation of the library, as `haskott-VERSION-docs.tar.gz`, in the
format Hackage takes. [CONTRIBUTING.md](CONTRIBUTING.md) describes the
commit messages, the versions and how a release is made.

## Reference material

Sewell, Zappa Nardelli, Owens, Peskine, Ridge, Sarkar and Strniša, "Ott:
Effective tool support for the working semanticist", Journal of Functional
Programming 20(1), 2010. Ott's [manual](http://www.cl.cam.ac.uk/~pes20/ott/top2.html)
and its [repository](https://github.com/ott-lang/ott).

haskott is BSD-3-Clause licensed; see `LICENSE`.
