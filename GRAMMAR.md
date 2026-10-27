# Ott source grammar reference

This document specifies the syntax of Ott source files (`.ott`) in enough detail
to reimplement a compatible parser from scratch, and in enough detail to work
out why a given file is rejected. The reference implementation is Ott 0.34:
`src/grammar_lexer.mll`, `src/grammar_parser.mly`, and the rule-body
processing in `src/defns.ml` in Ott's repository. haskott reads the same
language; where it gives a construct a meaning Ott does not (quoted
elements, §3.4; `typst` homs, which are ordinary homs to this grammar) the
text says so.
Ott's own manual says of this grammar only that "the lexing of Ott source files
is context-dependent; this does not show that". This document shows it.

Ott parses a specification in two stages, and so does haskott:

* **Stage one**, this document: the *metalanguage*. It turns a file into
  declarations of metavariables, grammar rules with productions, binding
  specifications, homomorphisms, embedded code, subrule and substitution
  declarations, parsing priorities, and inductive definitions whose rules are
  kept as **lines of text**. Nothing in this stage depends on the user's
  grammar.
* **Stage two**, not covered here: *symbolic terms*. Once the grammar is known,
  each rule line, each function clause and each `[[ ... ]]` quotation is lexed
  with a lexer derived from the grammar (terminals are inferred from the
  productions, identifiers split into a declared root and a suffix) and parsed
  against it. There is no separate specification of that language; haskott's
  `Haskott.Term.Grammar` follows Ott's `src/new_term_parser.ml` construct by
  construct and its header is the closest thing to one.

Sections 1–5 specify the language. Section 6 is a checklist of the parts of the
reference implementation that a reimplementation must reproduce but that are
not visible in the grammar. Section 7 says what haskott's lossless tree keeps
that Ott discards, and section 8 how the corpus tests all of this.

Notation, used from §2 on: `A*` zero or more, `A+` one or more, `A?`
optional, `A (',' A)*` a comma-separated list. Token spellings are shown in
`code`; token names (`STRING`, `BLANKS`, `LINE`, `EOF`) are used where a
token has no fixed spelling. A lexeme such as `' '* '</'` means optional
spaces then `</`. Italics mark the metavariables of a rule (*rest*, *lhs*).
Alternatives are not ordered: an implementation that tries them in order
(PEG, recursive descent) must try the longer forms first wherever one
alternative is a prefix of another (`comp_bound`, `mse`, `element`,
`hom_inner`).

---

## Contents

1. [Overview](#1-overview)
2. [Lexical grammar](#2-lexical-grammar)
   - [Encoding](#21-encoding)
   - [Character classes](#22-character-classes)
   - [Lexer modes and how they change](#23-lexer-modes-and-how-they-change)
   - [Mode `metalang`](#24-mode-metalang)
   - [Mode `elements`](#25-mode-elements)
   - [Mode `hom` and `hom_star`](#26-mode-hom-and-hom_star)
   - [Mode `comp_bound`](#27-mode-comp_bound)
   - [Mode `bindspec`](#28-mode-bindspec)
   - [Mode `defnlang` (line-oriented)](#29-mode-defnlang-line-oriented)
   - [Comments](#210-comments)
3. [Syntactic grammar](#3-syntactic-grammar)
   - [Files and items](#31-files-and-items)
   - [Metavariables and index variables](#32-metavariables-and-index-variables)
   - [Grammar rules and productions](#33-grammar-rules-and-productions)
   - [Elements](#34-elements)
   - [Binding specifications](#35-binding-specifications)
   - [Homomorphisms](#36-homomorphisms)
   - [Embedded code](#37-embedded-code)
   - [Subrules, context rules, substitutions, free variables](#38-subrules-context-rules-substitutions-free-variables)
   - [Inductive definitions](#39-inductive-definitions)
   - [Functions](#310-functions)
   - [Parsing priorities](#311-parsing-priorities)
   - [Hom sections](#312-hom-sections)
   - [Coq sections and variables](#313-coq-sections-and-variables)
4. [Rule bodies](#4-rule-bodies)
5. [What stage two receives](#5-what-stage-two-receives)
6. [Quirks a compatible parser must reproduce](#6-quirks-a-compatible-parser-must-reproduce)
7. [The lossless tree](#7-the-lossless-tree)
8. [Corpus](#8-corpus)

---

## 1. Overview

An Ott file is a sequence of **items**, each introduced by a keyword
(`metavar`, `indexvar`, `grammar`, `subrules`, `contextrules`,
`substitutions`, `freevars`, `defns`, `funs`, `embed`, `parsing`, `homs`,
`begincoqsection`, `endcoqsection`, `coqvariable`). Items are not terminated;
each one ends where the next keyword begins.

The lexer is **context-dependent**. It has several modes, and the token it
returns for a piece of text depends on the mode. The mode is changed by the
lexer itself when it returns certain tokens (not by the parser), so the mode
transitions are part of the lexical grammar and are listed in §2.3. The
practical effect is that a user rarely needs to quote anything: inside a
production the elements `\ x . t` are arbitrary whitespace-separated strings,
inside a hom `{{ tex \lambda [[x]] }}` the text is kept verbatim except for
`[[ ]]`, and inside a definition each rule is read line by line.

Whitespace is discarded in every mode except inside homs, where runs of blanks
are tokens (`BLANKS`) because the text is passed through to a proof assistant
or to a typesetter, and in the line-oriented mode, where whole lines are tokens.

The parser is an LALR(1) grammar (ocamlyacc). It is given in §3 as EBNF with
token spellings; it is unambiguous once the lexer modes are accounted for.

## 2. Lexical grammar

### 2.1 Encoding

Ott reads bytes and never decodes them. Identifiers are ASCII (§2.2); any other
byte is accepted only inside strings (production elements, hom text, lines),
where it is passed through unchanged. haskott reads UTF-8 and keeps token text
as `Text`; the lexical rules below are stated on characters, and for the ASCII
classes they are the same thing. A byte sequence that is not valid UTF-8 is
rejected by haskott and accepted by Ott. This, and one end-of-input case in
`defnlang` (§2.9), are the two intended divergences. The corpus has one
file that is not UTF-8, `examples/ocaml_light/library.ott`; Ott rejects it
too, for the `-` on its first line (`-*-LaTeX-*-`, §2.4), so the two verdicts
agree there for different reasons.

### 2.2 Character classes

| name | definition |
|---|---|
| `newline` | `\n`, `\r`, or `\r\n` (one token in `metalang`; a line terminator in `defnlang`) |
| `nnws` | non-newline whitespace: space, tab (`\t`), form feed (`\f`) |
| `whitespace` | `nnws` or `\n` or `\r` |
| `identchar` | `A`–`Z`, `a`–`z`, `0`–`9`, `_`, `'` |
| `pre_ident` | `identchar+` |
| `maybe_quoted_ident` | `pre_ident`, or `'` `pre_ident` `'`, or `''` (the empty quoted identifier) |
| `string` | one or more characters that are not `whitespace` |

Note that `'` is an identifier character, so `t'` and `x''` are identifiers,
and `'t_'` is a quoted identifier whose content is `t_`. For the same reason
`maybe_quoted_ident` matches exactly what `identchar+` matches: the quoted
alternatives add nothing, `'a'b'` is one identifier (dequoted to `a'b`),
`'a b'` is two, and a lone `'` is an identifier that dequoting leaves alone.
The last case decides where Ott reports the error in
`examples/ocaml_light/syntax.ott`, whose `'<<'` closes a block comment. Because
`-` is not an identifier character, `tex-preamble` is not an identifier (it is
a `string`, which is why hom names can contain it: hom names are lexed in
`hom` mode). The class `string` is a character class; the token `STRING` of
each mode is defined by that mode's table and is narrower in `hom` mode.

**Dequoting.** Where a rule below says a token is *dequoted*, a lexeme of the
form `'…'` with at least two characters yields the content between the quotes,
and any other lexeme yields itself. `''` dequotes to the empty string. The
original spelling is kept alongside (the parser uses it to tell a quoted
element from an unquoted one, §3.4).

**Longest match.** Within a mode the lexer takes the longest matching lexeme;
among rules matching the same length the first listed wins. Consequences that
matter: in `metalang` the keyword rules and the identifier rule compete, so
`grammars` is an identifier but `grammar` is a keyword; a nonterminal that
would spell a keyword must be quoted (`'left'`, `'in'`, `'fun'`), and is
dequoted to the bare name. In `elements` mode `::` is a token but `'::'` and
`::=` are strings.

### 2.3 Lexer modes and how they change

| mode | entered by | left by |
|---|---|---|
| `metalang` | start of file; `::` in `elements`; `}}` in `hom` (when entered from `metalang`); `+)` in `bindspec`; a section keyword at the start of a line in `defnlang` | see below |
| `elements` | `\|` or `defn` or `fun` in `metalang`; `defn` or `fun` as first word of a line in `defnlang` | `::` → `metalang` |
| `hom` | `{{` in `metalang`; `{{com` or `{{ com` as first word of a line in `defnlang` | `}}` → the mode it was entered from |
| `hom_star` | `{{*` in `metalang` | `*}}` → `metalang` |
| `comp_bound` | ` *</` (optional spaces then `</`) in `hom` or `hom_star` | `/>` → the hom mode it was entered from |
| `bindspec` | `(+` in `metalang` | `+)` → `metalang` |
| `defnlang` | `by` in `metalang` | a line whose first word is a section keyword → `metalang`; `defn`/`fun` → `elements`; `{{com` → `hom` (returning to `defnlang`) |
| `comments` | `>>` in `metalang`, `bindspec` or (at line start) `defnlang` | matching `<<` → the mode it was entered from |

Only the transitions listed exist. In particular `{{` inside `elements` is a
string, `(+` inside `hom` is text, and `|` inside `bindspec` is a lexing error.

### 2.4 Mode `metalang`

Whitespace and comments are discarded (they are *interstitial*; §7 says how
haskott keeps them). Rules, in priority order for equal-length matches:

| lexeme | token | effect |
|---|---|---|
| `nnws+` | interstitial | |
| `newline` | interstitial | |
| `>>` | begins a block comment (§2.10) | mode `comments` |
| `%` … `newline` | interstitial (line comment, newline included) | |
| `,` | `COMMA` | |
| `::=` | `CCE` | |
| `\|` | `BAR` | mode `elements` |
| `{{` | `DOUBLELEFTBRACE` | mode `hom`, returning to `metalang` |
| `}}` | `DOUBLERIGHTBRACE` | |
| `::` | `COLONCOLON` | |
| `<::` | `LTCOLONCOLON` | |
| `_::` | `UNDERSCORECOLONCOLON` | |
| `embed` `homs` `metavar` `indexvar` `grammar` `subrules` `contextrules` `substitutions` `single` `multiple` `freevars` `parsing` `begincoqsection` `endcoqsection` `coqvariable` `left` `right` `non` `defns` `funs` | the keyword | |
| `<=` | `LTEQ` | |
| `defn` | `DEFN` | mode `elements` |
| `fun` | `FUNDEFN` | mode `elements` |
| `by` | `BY` | mode `defnlang` |
| `(+` | `BIND_LEFT_DELIM` | mode `bindspec` |
| `{{*` | `DOUBLELEFTBRACE` | mode `hom_star` |
| `*}}` | `DOUBLERIGHTBRACE` | |
| `maybe_quoted_ident` | `STRING` (dequoted; spelling kept) | |
| end of input | `EOF` | |

Anything else (for example a bare `-`, `(`, `[`, or a non-ASCII character) is a
lexing error in this mode.

The `%` comment rule requires a terminating newline. A `%` comment on the last
line of a file with no final newline does not match, and Ott reports a lexing
error. (In `defnlang` and `bindspec` the same comment at end of input is
accepted.)

### 2.5 Mode `elements`

Used for the elements of a production and for the form of a `defn` or `fun`.
Tokens must be whitespace-separated; whitespace is discarded; there are no
comments.

| lexeme | token | effect |
|---|---|---|
| `nnws+`, `newline` | interstitial | |
| `::` | `COLONCOLON` | mode `metalang` |
| `..` `...` `....` | `DOTDOT` `DOTDOTDOT` `DOTDOTDOTDOT` | |
| `</` `//` `/>` | `COMP_LEFT` `COMP_MIDDLE` `COMP_RIGHT` | |
| `IN` | `COMP_IN` | |
| `string` | `STRING` (dequoted; spelling kept) | |
| end of input | `EOF` | |

Because `string` is any run of non-whitespace, every element is one token:
`\`, `x`, `.`, `t`, `(`, `{`, `-->`, `'in'`, `'::'`. The special tokens win
only when they are the whole run (`..` is `DOTDOT`; `..x` is a string) except
that longest match makes `..` lose to `...` and `....`.

### 2.6 Mode `hom` and `hom_star`

Used for the body of a homomorphism `{{ name body }}` and an embed block.
Blanks are preserved as tokens because the body is output verbatim.

`hom`:

| lexeme | token | effect |
|---|---|---|
| `nnws+` | `BLANKS` | |
| `newline` | `BLANKS` | |
| `[[` | `DOUBLELEFTBRACKET` | |
| `]]` | `DOUBLERIGHTBRACKET` | |
| `{{` | `DOUBLELEFTBRACE` | (nested; the parser does not accept it, so this is an error in practice) |
| `}}` | `DOUBLERIGHTBRACE` | return to the entering mode |
| `[` `]` `{` `}` | `STRING` of that one character | |
| `..` `...` `....` | `DOTDOT` `DOTDOTDOT` `DOTDOTDOTDOT` | |
| `' '* '</'` (optional spaces then `</`) | `COMP_LEFT`; the spaces are part of the lexeme and are not a `BLANKS` token | mode `comp_bound`, returning here |
| `.` | `STRING` `"."` | |
| one or more characters other than `whitespace` `[` `]` `{` `}` `.` | `STRING` (not dequoted: `{{ tex 'x' }}` keeps its quotes) | |
| end of input | `EOF` | |

`hom_star` is the same with `*}}` closing instead of `}}`, with `{`, `}` and
`{{` as ordinary characters (its `STRING` is one or more characters other
than `whitespace` `[` `]` `*` `.`), and with `*` as a one-character `STRING`
so that `*}}` can be recognised by longest match.

Longest match applies here too: `' '* '</'` is `COMP_LEFT` only when the
string rule does not match more, so `[[ </ x_i // i /> ]]` opens a
comprehension and `[[</x_i//i/>]]` lexes `</x_i//i/>` as one `STRING`.

A hom's text is therefore split into runs separated at brackets, braces, dots
and whitespace, and the original text is recovered by concatenation, except
around a comprehension: the spaces before `</` are swallowed by `COMP_LEFT`
and the whitespace between `</` and `/>` is discarded (§2.7). The split
exists so that `[[x]]` lexes as `[[`, `x`, `]]` without spaces around it.

### 2.7 Mode `comp_bound`

Inside a hom, after `</`, up to and including `/>`. Whitespace is discarded
and, as in `elements`, every token must be a whole whitespace-delimited run.

| lexeme | token | effect |
|---|---|---|
| `whitespace+` | interstitial | |
| `..` `...` `....` | `DOTDOT` `DOTDOTDOT` `DOTDOTDOTDOT` | |
| `</` `//` | `COMP_LEFT` `COMP_MIDDLE` | |
| `/>` | `COMP_RIGHT` | back to the hom mode |
| `IN` | `COMP_IN` | |
| `string` | `STRING` (not dequoted) | |
| end of input | `EOF` | |

The whole-run rule has a sharp edge: `x_i//i/>` is one `STRING`, so the mode
is left only by a free-standing `/>`. In `{{ coq [[ </x_i//i/> ]] }}` the
space before `</` makes it `COMP_LEFT` (§2.6), the rest of the quotation is
one string, and Ott keeps lexing in this mode past `}}` and the following
lines until it meets a free-standing `/>` or the end of the file; the
syntax error is reported there, not in the hom. Tokens inside a
comprehension must be spaced: `[[ </ x_i // i /> ]]`.

The nonterminal `comp_bound` of §3.4 is parsed from the tokens of this mode
inside a hom, from `elements` tokens in a production and from `bindspec`
tokens in a bindspec; only the last two are dequoted.

### 2.8 Mode `bindspec`

Between `(+` and `+)`. Whitespace is discarded; comments are allowed.

| lexeme | token | effect |
|---|---|---|
| `nnws+`, `newline` | interstitial | |
| `%` to end of line | interstitial (the newline is consumed by the next rule) | |
| `>>` | block comment (§2.10) | |
| `+)` | `BIND_RIGHT_DELIM` | mode `metalang` |
| `bind` `in` `names` `distinctnames` `union` | the keyword | |
| `=` `#` `(` `)` | `EQ` `HASH` `LPAREN` `RPAREN` | |
| `{}` | `EMPTY` | |
| `..` `...` `....` | dots | |
| `</` `//` `/>` | comp delimiters | |
| `IN` | `COMP_IN` | |
| `maybe_quoted_ident` | `STRING` (dequoted; spelling kept) | |
| end of input | `EOF` | |

Anything else (`{{`, `|`, `[`, `-`, …) is a lexing error in this mode.

### 2.9 Mode `defnlang` (line-oriented)

Entered after `by`. The rest of the `by` line, and every following line until
a line whose first word is a section keyword, is lexed **one line at a time**.
A line's token is decided by its shape:

| line shape | token |
|---|---|
| `nnws*` `newline` | `BLANKLINE` (text includes the newline) |
| `nnws*` `%` … `newline` | `COMMENTLINE` (text includes the newline) |
| `nnws*` `%` … end of input | `EOF` |
| `nnws*` `>>` `nnws*` `newline` | begins a block comment (§2.10); lexing resumes in `defnlang` immediately after the closing `<<`, which need not be at a line start |
| `nnws*` `----` `'-'*` *rest* (`newline` or end of input), *rest* non-empty | `LINELINE` (dashes, rest, terminator). Because *rest* must be non-empty, a line of exactly `----` is a `LINE`, and a line of five or more dashes alone is a `LINELINE` whose *rest* is a dash (Ott's lexer binds the run of dashes greedily and gives one back), which then fails to parse as an annotation (§4) |
| `nnws+` end of input | `LINE` (whitespace only, no terminator) |
| any other non-empty line | see below |
| end of input | `EOF` |

For "any other non-empty line", the lexer takes the first whitespace-delimited
word of the line:

| first word | effect |
|---|---|
| `grammar` `embed` `homs` `metavar` `indexvar` `subrules` `contextrules` `substitutions` `freevars` `parsing` `defns` `begincoqsection` `endcoqsection` `coqvariable` `funs` | the keyword token; the rest of the line is re-lexed in `metalang` (the definition has ended) |
| `defn` `fun` | the keyword token; the rest of the line is re-lexed in `elements` |
| `{{com` | `DEFNCOM`; the rest of the line is re-lexed in `hom`, returning to `defnlang` |
| `{{` followed by the word `com` | `DEFNCOM`; the rest after `com` is re-lexed in `hom`, returning to `defnlang` |
| anything else (including `{{` followed by another word) | `LINE` (text without the terminator, terminator kept separately) |

A dashed line's *rest* (everything after the run of `-`) is later parsed on its
own with the `metalang` lexer as the rule's annotation (§4). It is lexed as a
string of its own, without the line's terminator, so a `%` comment on a
dashed line (`---- :: one % a comment`) is a lexing error (§2.4).

**End of input.** Ott's first-word scan reads one character past the end
when the first word of the last line runs to the end of the file, so a last
line that is a single word with no final newline (`ok` as the last
conclusion, `{{com` or `{{` alone) is a lexing error in Ott; the same line
followed by a newline, or a multi-word last line without one, is accepted.
haskott accepts the single-word case. This is the second intended
divergence (§2.1); the `corpus` suite pins it.

### 2.10 Comments

Two comment forms exist in the modes that allow comments (`metalang`,
`bindspec`, and `defnlang` as whole lines):

* **Line comments** `%` to the end of the line.
* **Block comments** `>>` to the matching `<<`. They nest: each `>>` inside
  opens another level. A `%` inside a block comment hides the rest of its line,
  so `<<` after a `%` on the same line does not close anything. An unclosed
  block comment at end of input is a lexing error (Ott prints a warning
  first, then the error). `examples/ocaml_light/syntax.ott` is rejected by
  this rule: a `>>` on line 737 is followed by a hidden `%d<<` and is only
  closed by a `'<<'` on line 840, so the rest of the file is a comment.

There are no comments in `elements`, `hom`, `hom_star` or `comp_bound` mode:
`%` there is an ordinary character.

## 3. Syntactic grammar

In this section `ident` is a `STRING` token from `metalang` or `bindspec`
mode (a dequoted `maybe_quoted_ident`) and `string` is a `STRING` token from
`elements`, `hom` or `comp_bound` mode (not dequoted). Ott's parser has one
`STRING` token, so where the grammar below writes `ident` for a token that
the lexer produced in `hom` or `comp_bound` mode (`hom_inner`, and
`comp_bound` inside a hom) it is that mode's string, not dequoted; the text
says so at each place.

### 3.1 Files and items

```
file  ::= item* EOF
item  ::= metavardefn
        | 'grammar'          rule*
        | 'defns'            defnclass
        | 'funs'             fundefnclass
        | 'subrules'         subrule*
        | 'contextrules'     contextrule*
        | 'substitutions'    substitution*
        | 'freevars'         freevar*
        | 'embed'            embedmorphism*
        | 'parsing'          parsing_annotation*
        | 'homs'             hom_section
        | 'begincoqsection'  ident
        | 'endcoqsection'    ident
        | 'coqvariable'      ident
```

Every list of declarations under a keyword may be empty. Because items are not
terminated, `grammar` followed directly by `defns` is a grammar item with no
rules.

### 3.2 Metavariables and index variables

```
metavardefn ::= 'metavar'  names '::=' hom*
              | 'indexvar' names '::=' hom*
names       ::= name_hom (',' name_hom)*
name_hom    ::= ident hom*
```

The first name is the primary root; the others are synonyms. Each name may carry
its own homs (`metavar var {{ tex x }}, x ::= …`), in addition to the homs after
`::=` that apply to the declaration. In the corpus no file uses per-name homs.

### 3.3 Grammar rules and productions

```
rule ::= names '::' ident '::=' hom* prod*
prod ::= '|' element* '::' ident* '::' ident bindspecs hom*
```

In `rule`, the `ident` after `::` is the production-name prefix (`'t_'`, or
`''` for none); it is lexed in `metalang`, so it is usually quoted. The homs
after `::=` are the rule's homs (`{{ com term }}`, `{{ coq … }}`).

In `prod`, `'|'` switches the lexer to `elements` mode, so `element*` is
whitespace-separated strings up to the first bare `::`, which switches back.
The `ident*` between the two `::` are the production's *categories* (flags),
free identifiers; those with meaning to Ott are `M` (meta production), `S`
(syntactic sugar), `I` (ignored for proof assistant output), `L`, `J`, `JT`.
Categories may be separated by blanks only, no commas. The `ident` after the
second `::` is the production name, to which the rule's prefix is prepended.

A production ends where the next `|`, the next rule or the next item keyword
begins. `prod*` and `rule*` are both lists with no separators, and the
LALR(1) parser needs one token to decide: after a production's homs and
bindspecs, `|` continues the rule, a `STRING` begins a new rule (its
`names`), and anything else ends the `grammar` item. The element list of a
production may be empty (`|   :: d :: nil`).

### 3.4 Elements

```
element    ::= string                              -- a terminal, nonterminal or metavariable (decided in stage two)
             | dots                                -- '..' | '...' | '....'
             | '</' element* '//' comp_bound '/>'
             | '</' element* '//' ident '//' comp_bound '/>'
comp_bound ::= ident
             | ident 'IN' ident
             | ident 'IN' ident dots ident
dots       ::= '..' | '...' | '....'
```

The three dot forms differ only in length; they denote list forms whose
elements are separated by nothing (`..`), by the previous element repeated
(`...`), or the longer form (`....`). Stage two gives them meaning. Here they
are three distinct tokens because `elements` mode lexes them so.

A `string` element whose spelling starts with `'` and has at least two
characters (`'in'`, `'::'`, `'..'`) is a **quoted element**. Its dequoted
content (§2.2; `'foo` without a closing quote is a quoted element whose
content is `'foo`) is what is matched in terms. Ott keeps nothing but that
content: a quoted element is then read like any other identifier, so `'in'`
with a metavariable `i` and an index variable `n` is that metavariable with
suffix `n`, and quoting only serves to write an Ott keyword such as `in` or
`..` as an element at all. haskott keeps the quoting as a flag and, in stage
two, treats a quoted element as a terminal unless its content is exactly a
declared metavariable or nonterminal root, so `'in'` is the terminal `in`.
A file that relies on this is not a stock Ott file. In this grammar it is
simply a `string` with a flag.

### 3.5 Binding specifications

```
bindspecs ::= ( '(+' bindspec* '+)' )*
bindspec  ::= 'bind' mse 'in' ident
            | ident '=' mse
            | 'names' '(' mse ')' '=' 'names' '(' mse ')'
            | 'names' '(' mse ')' '#' 'names' '(' mse ')'
            | 'distinctnames' '(' mse ')'
mse       ::= ident
            | ident dots ident
            | '</' ident '//' comp_bound '/>'
            | ident '(' ident ')'
            | ident '(' ident dots ident ')'
            | ident '(' '</' ident '//' comp_bound '/>' ')'
            | ident '</' ident '//' comp_bound '/>'
            | mse 'union' mse
            | '{}'
```

`union` is right-associative. Several `(+ … +)` groups may follow one
production; they are concatenated. The `names` and `distinctnames` forms are
parsed but not supported by Ott's back ends; one corpus file has `names`
commented out and none uses `distinctnames`.

### 3.6 Homomorphisms

```
hom         ::= '{{' hom_name hom_el* '}}'
              | '{{*' hom_name hom_el* '*}}'
hom_name    ::= BLANKS? string BLANKS
hom_el      ::= '[[' hom_inner ']]'
              | string | BLANKS | dots
hom_inner   ::= (ident | BLANKS)*
              | (ident | BLANKS)* dots (ident | BLANKS)*
              | '</' (ident | BLANKS)* '//' comp_bound '/>' BLANKS*
```

`hom_name` requires a `BLANKS` token after the name, so `{{com}}` is a parse
error and `{{ com }}` and `{{com }}` are accepted. The name is a `string` in
`hom` mode, so it may contain `-` (`coq-equality`, `tex-preamble`,
`repr-locally-nameless`). Names have no syntax of their own; which names mean
what is a matter for the checker and the back ends (the corpus uses `com`,
`tex`, `coq`, `isa`, `hol`, `lem`, `ocaml`, `lex`, the `*var` family and a
dozen more; `typst` is haskott's).

Inside `[[ ]]` the identifiers are nonterminals and metavariables with suffixes
(`t1`, `x`, `t'`) or, for locally nameless homs, several of them (`[[x t1]]`);
they are lexed as `hom`-mode strings here and resolved in stage two. Any `[`,
`]`, `{`, `}`, `.` or whitespace inside a hom body splits the text; the
original is recovered by concatenating the tokens in order.

### 3.7 Embedded code

```
embedmorphism ::= '{{' hom_name embed_el* '}}'
embed_el      ::= '[[' (string | BLANKS)* ']]'
                | string | BLANKS | dots
```

The same lexing as homs. The body is passed to the named back end
(`{{ coq … }}`, `{{ tex-preamble … }}`, `{{ typst-preamble … }}`), with each
`[[ … ]]` replaced by the translation of the symbolic term it contains (stage
two). Unlike `hom_inner`, the inside of an embed's `[[ ]]` admits only
strings and blanks: `..` and `</` there are tokens the grammar does not
accept, so `[[ x1 .. xn ]]` is a syntax error inside an embed and legal
inside a hom. The `>>` of a Coq `=>` inside an embed is ordinary text; the
`comments` mode is never entered from `hom` mode.

### 3.8 Subrules, context rules, substitutions, free variables

```
subrule      ::= ident '<::' ident hom*
contextrule  ::= ident '_::' ident '::' ident
substitution ::= ('single' | 'multiple') ident ident '::' ident hom*
freevar      ::= ident ident '::' ident hom*
```

`subrule`: lower root, upper root. `contextrule`: context root, target root,
hole root. `substitution`: the nonterminal being substituted in, the
metavariable or nonterminal being substituted for, and the generated function's
name. `freevar`: likewise, with the function name after `::`.

### 3.9 Inductive definitions

```
defnclass ::= ident '::' ident '::=' hom* defn*
defn      ::= 'defn' element* '::' ident* '::' ident '::' ident hom* 'by' rule_body
```

In `defnclass` the first `ident` is the class name (`Jop`) and the second is
the prefix prepended to its rules' names (`''` or `'red_'`); the homs are the
class's. In `defn`, `'defn'` switches to `elements` mode, so the judgement form
(`t1 --> t2`) is whitespace-separated strings up to the first bare `::`. Then
come the categories (as in a production), the definition's name, the prefix for
its rule names, its homs, and `by`, which switches to `defnlang` mode. The
`rule_body` is given in §4.

### 3.10 Functions

```
fundefnclass ::= ident '::=' hom* fundefn*
fundefn      ::= 'fun' element* '::' ident '::' ident hom* 'by' BLANKLINE clause_line*
clause_line  ::= LINE | COMMENTLINE | BLANKLINE
```

`fun` switches to `elements` mode for the function's form (`dom ( EB )`); the
`ident` after the first `::` is the result nonterminal, the one after the
second is the function name. The clauses start after the newline that ends
the `by` line (it is the required `BLANKLINE`) and run until the next keyword
line. Each `LINE` is one clause, of the form *lhs* `===` *rhs*, parsed in stage
two as a symbolic term of a production synthesised from the function's form.

### 3.11 Parsing priorities

```
parsing_annotation ::= ident ('<=' | 'left' | 'right' | 'non') ident
```

Both identifiers are production names (with their rule's prefix). `left`,
`right` and `non` are keywords in `metalang` mode, so a production named
`left` cannot be referred to here without quoting (`'left'`).

### 3.12 Hom sections

```
hom_section      ::= ident hom_section_item*
hom_section_item ::= '::' ident bindspecs hom*
```

Attaches bindspecs and homs to existing productions after the fact: the
`ident` after `homs` is a production-name prefix, each item names a production
by its unprefixed name. Used by the `-merge` workflow to keep back-end data in
separate files.

### 3.13 Coq sections and variables

```
'begincoqsection' ident
'endcoqsection'   ident
'coqvariable'     ident
```

Pass-through markers for the Coq back end. No corpus file uses them.

## 4. Rule bodies

After `by`, the body of a definition is the sequence of `defnlang` tokens up to
the next keyword line. Its structure, as the parser imposes it:

```
rule_body ::= ( BLANKLINE+ drule )* BLANKLINE*
drule     ::= premise_lines LINELINE conclusion_lines     -- a lined rule
            | (LINE | COMMENTLINE)+                        -- a lineless rule
            | DEFNCOM embed_el* '}}'                       -- a comment block
premise_lines    ::= (LINE | COMMENTLINE)*
conclusion_lines ::= (LINE | COMMENTLINE)*
```

(`drule`, Ott's name, to keep it apart from the grammar `rule` of §3.3.)
Rules are separated by one or more blank lines, and the first rule needs at
least one blank line before it; the newline that ends the `by` line is one
(`by` may not be followed by anything else on its line, or that text becomes a
`LINE` and the first rule is not preceded by a blank line, which is a parse
error). Comment lines (`%`) may appear anywhere inside a rule and are dropped.
A lineless rule made of comment lines only parses and produces nothing. Two
dashed lines in one block are a parse error, and so are a `LINELINE` or a
`DEFNCOM` inside a `fun` body (§3.10), whose lines are plain.

**Lined rules.** The usual form:

```
    premise
    premise
    ---------------------- :: name
    conclusion
```

* The `LINELINE`'s *rest* (after the dashes) is lexed on its own, without
  the line's terminator, with the `metalang` lexer, and parsed as
  `ident* '::' ident hom* EOF`: zero or more category names, the rule name,
  and homs (`------- S :: paren`, `------- :: pair {{ com pairing }}`). A `%`
  comment after the name is therefore a lexing error (§2.4). The rule's full
  name is the class prefix, then the definition prefix, then this name.
* The premise lines are the `LINE`s before the dashes, one premise per line.
  Each premise's text is first stripped of an optional trailing premise name
  `[[:name]]` (where `name` is a letter followed by letters and digits, and
  only trailing spaces may follow it); this names the premise for the Coq back
  end. If what remains starts, after optional spaces, with `{{` and
  contains `}}` followed by optional spaces (Ott's test is a regular
  expression anchored at the start only, so `{{ coq True }} junk` is
  accepted and the junk is silently dropped), the premise is *embedded
  prover code*: the text between the braces is lexed with Ott's `filter`
  lexer, the one used for the `-tex_filter` documents, in which only `[[`,
  `]]` and whitespace are special (no dots, no `</`, no splitting at `{ } .`,
  and `[[[` and `]]]` pass a literal `[[` and `]]` through), and each
  `[[ … ]]` is a symbolic term. Otherwise the whole line is a symbolic term
  of the `formula` grammar.
* The conclusion is the `LINE`s after the dashes. There must be exactly one;
  none is the error "rule with no conclusion" and more than one "rule with
  multiple conclusions". It is a symbolic term of the judgement form being
  defined.

**Lineless rules.** A block of lines with no dashed line. Ott joins the lines
with single spaces, parses the result as one formula, and makes a rule with no
premises named `fake` plus a counter, in category `F`. The code calls this a
test-harness hack. haskott accepts it for compatibility and reports it as a
diagnostic.

**Comment blocks.** A block beginning `{{ com` is a `DEFNCOM`: its body, up to
`}}`, is typeset among the rules. Its `[[ … ]]` parts are symbolic terms.

## 5. What stage two receives

Stage one leaves these as text for the grammar-derived lexer and parser:

| where | text | parsed in stage two as |
|---|---|---|
| premise line | the line, minus a trailing `[[:name]]` | a term of the `formula` grammar, or embedded code with `[[ ]]` terms |
| conclusion line | the line | a term of the defined judgement's form |
| function clause line | the line | a term `lhs === rhs` |
| `[[ … ]]` in a hom | the identifiers between the brackets | nonterminals and metavariables with suffixes, possibly with dots or a comprehension |
| `[[ … ]]` in an embed or comment block | the text between the brackets | a term of the `user_syntax` grammar |
| production elements | each string | a terminal, nonterminal or metavariable, by the ident lexer; a quoted string is a terminal unless it is exactly a root |

Everything else (declaration structure, categories, names, prefixes, bindspec
structure, hom structure) is fully determined in stage one.

## 6. Quirks a compatible parser must reproduce

One line each; the section that specifies the quirk, and the test that pins
it (`corpus` is the `inlineCases` of `test/Corpus.hs`; a corpus file is
named where one exercises it).

* Keywords are reserved only in the mode that has them: `left`, `right`,
  `non`, `single`, `multiple`, `by` in `metalang`; `bind`, `in`, `names`,
  `distinctnames`, `union` in `bindspec`; `IN`, the dots and the
  comprehension delimiters in `elements` and `comp_bound`. Elsewhere they are
  ordinary, so `in :: '' ::=` needs no quoting (§2.4, §2.5, §2.8).
* `%` comment at end of file without a newline: lexing error in `metalang`,
  accepted in `defnlang` and `bindspec` (§2.4; corpus).
* A single-word last line with no final newline in `defnlang` is a lexing
  error in Ott and accepted by haskott: the declared divergence (§2.9;
  corpus).
* An unclosed block comment is a lexing error, after a warning (§2.10;
  corpus, `examples/ocaml_light/syntax.ott`).
* `%` inside a block comment hides `<<` on the rest of its line (§2.10;
  `examples/ocaml_light/syntax.ott`).
* A rule line whose first word is a section keyword ends the definition;
  there is no escape (§2.9).
* Dashed lines are recognised anywhere in `defnlang`, so a premise cannot
  begin with `----`; exactly `----` alone is a `LINE` (§2.9).
* A `%` comment on a dashed line is a lexing error: the annotation is lexed
  without its newline (§2.9, §4; corpus).
* `{{ com` at a line start inside a definition is a comment block (§2.9).
* `by` must end its line, or the first rule has no blank line before it
  (§4; corpus).
* Hom names need a following blank: `{{com}}` is a parse error (§3.6;
  corpus).
* `>>` inside a definition starts a block comment only when alone on its
  line (§2.9).
* Nested `{{` inside a hom is a token the grammar does not accept; braces in
  hom text must be single (§2.6).
* `[[ </x_i//i/> ]]` with a space before `</` never leaves `comp_bound`
  mode; the error is reported lines later (§2.7; corpus).
* `..` and `</` inside an embed's `[[ ]]` are syntax errors (§3.7; corpus).
* A lineless rule of comment lines only parses and produces nothing (§4;
  corpus).
* An embedded premise `{{ … }}` is recognised by a start-anchored match, so
  trailing text after `}}` is dropped (§4; corpus).
* `''` is an identifier, the empty one (§2.2).
* Ott discards whitespace and comments in `metalang`, `elements`, `bindspec`
  and `comp_bound` before the parser sees them; positions in its error
  messages come from the lexer's line counter (§2).

## 7. The lossless tree

haskott's parser builds a lossless tree (a graft green tree, in which
whitespace and comments are tokens) directly from the rules above, and the
checked specification is a projection of it. Every interstitial of §2 is a
trivia token, the `BLANKS` of hom bodies are the same trivia kinds, and a
`LINE` is a token without its terminator; rendering an unedited tree yields
the input exactly, on every file of §8, and still does after stage two has
replaced each rule line by the subtree of its term. The token and node
kinds, and the two rules that place trivia (an item owns the whitespace in
front of it, the trivia to the end of its last line, and the comment lines
after it indented past its first column; everything else belongs to the
innermost node whose span contains it), are in the header of
`Haskott.Syntax.Parser`.

## 8. Corpus

Ott 0.34 ships 116 `.ott` files under `tests/` and 38 under `examples/`.
They are the acceptance corpus. `test/ott-acceptance.tsv` records Ott's
verdict on each: `accepted`, `other-error` (Ott parses the file and rejects
it later) or `parse-error`. haskott must parse every file of the first two
classes and render it back byte for byte, and reject every file of the
third; `test/first-diagnostics.tsv` records the first problem it reports
for each. The differential (`haskott-differential`) then compares the parse
itself, the checked specification, every term parse and the TeX and prover
output with Ott's on every file Ott parses. Of the constructs
in §3, `contextrules`, `distinctnames`, `begincoqsection`, `endcoqsection`
and `coqvariable` appear in no corpus file, `names` only commented out
(`tests/binding.4.ott`), and `funs` in one (`examples/ocaml_light/funex.ott`);
every other construct is exercised.
