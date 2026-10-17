# Ott source grammar reference

This document specifies the syntax of Ott source files (`.ott`) in enough detail
to reimplement a compatible parser from scratch. The reference implementation is
Ott 0.34 as extended on the `typst` work of
[andreabedini/ott](https://github.com/andreabedini/ott) (commit `1200eab`,
"fix: make quoted tokens in productions terminals"): `src/grammar_lexer.mll`,
`src/grammar_parser.mly`, and the rule-body processing in `src/defns.ml`.
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
  against it. That language is specified separately.

Sections 1–5 specify the language. Section 6 records the parts of the reference
implementation that a reimplementation must reproduce but that are not visible
in the grammar. Section 7 says what haskott's lossless tree keeps that Ott
discards.

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
rejected by haskott and accepted by Ott; this is the one intended divergence.

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
and `'t_'` is a quoted identifier whose content is `t_`. Because `-` is not an
identifier character, `tex-preamble` is not an identifier (it is a `string`,
which is why hom names can contain it: hom names are lexed in `hom` mode).

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
| ` *</` (spaces then `</`) | `COMP_LEFT` | mode `comp_bound`, returning here |
| `.` | `STRING` `"."` | |
| one or more characters other than `whitespace` `[` `]` `{` `}` `.` | `STRING` | |
| end of input | `EOF` | |

`hom_star` is the same with `*}}` closing instead of `}}`, with `{`, `}` and
`{{` as ordinary characters, and with `*` as a one-character `STRING` so that
`*}}` can be recognised by longest match.

A hom's text is therefore split into runs separated at brackets, braces, dots
and whitespace, and the original text is recovered by concatenation. The split
exists so that `[[x]]` lexes as `[[`, `x`, `]]` without spaces around it.

### 2.7 Mode `comp_bound`

Inside a hom, after `</`, up to and including `/>`: whitespace is discarded;
`..` `...` `....` `</` `//` `IN` are tokens; `/>` is a token and returns to the
hom mode; any other run of non-whitespace is a `STRING`.

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
| `nnws*` `----` `-*` *rest* (`newline` or end of input) | `LINELINE` (dashes, rest, terminator) |
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
own with the `metalang` lexer as the rule's annotation (§4).

### 2.10 Comments

Two comment forms exist in the modes that allow comments (`metalang`,
`bindspec`, and `defnlang` as whole lines):

* **Line comments** `%` to the end of the line.
* **Block comments** `>>` to the matching `<<`. They nest: each `>>` inside
  opens another level. A `%` inside a block comment hides the rest of its line,
  so `<<` after a `%` on the same line does not close anything. An unclosed
  block comment at end of input is a warning and ends the file.

There are no comments in `elements`, `hom`, `hom_star` or `comp_bound` mode:
`%` there is an ordinary character.

## 3. Syntactic grammar

Notation: `A*` zero or more, `A+` one or more, `A?` optional, `A (, A)*` a
comma-separated list. Token spellings are shown in `code`; `ident` is a
`STRING` token from `metalang` or `bindspec` mode (a dequoted
`maybe_quoted_ident`); `string` is a `STRING` token from `elements` or `hom`
mode. Where a token's mode matters it is stated.

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

A production ends where the next `|`, the next rule (`names ::`) or the next
item keyword begins. Because `prod*` and `rule*` are both lists with no
separators, the parser decides that a new rule starts when it sees
`ident (',' ident)* '::'`: an `ident` followed by `::` after a production's
homs is the start of a rule. This is unambiguous because a production's homs
are `{{ }}`-delimited and its bindspecs `(+ +)`-delimited.

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

A `string` element whose spelling was quoted (`'in'`, `'::'`, `'..'`) is a
**quoted element** (fork extension, Ott commit `1200eab`). Its dequoted content
is what is matched in terms; stage two treats it as a terminal unless the
content is exactly a declared metavariable or nonterminal root. The purpose is
to write terminals such as `in`, which would otherwise lex in terms as the
metavariable `i` with suffix `n`, and `..`, which would otherwise be a dot
form. In this grammar it is simply a `string` with a flag.

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
parsed but not supported by Ott's back ends; one corpus file has them commented
out.

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
`tex`, `typst`, `coq`, `isa`, `hol`, `lem`, `ocaml`, `ich`, `ichl`, `icho`,
`ic`, `lex`, `texvar`, `typstvar`, `isavar`, `holvar`, `lemvar`, `ocamlvar`,
`coq-equality`, `phantom`, `aux`, `quotient-remove`, `quotient-with`,
`menhir-start`, `menhir-prec`, `ocamllex`, `pp`, `pp-raw`, `tex-preamble`,
`isasyn`, `isaprec`, `coq-universe`, `repr-locally-nameless`, and others).

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
two). The `>>` of a Coq `=>` inside an embed is ordinary text; the `comments`
mode is never entered from `hom` mode.

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
rule_body ::= BLANKLINE* ( BLANKLINE+ rule )* BLANKLINE*
rule      ::= premise_lines LINELINE conclusion_lines     -- a lined rule
            | (LINE | COMMENTLINE) (LINE | COMMENTLINE)*   -- a lineless rule, at least one LINE
            | DEFNCOM embed_el* '}}'                       -- a comment block
premise_lines    ::= (LINE | COMMENTLINE)*
conclusion_lines ::= (LINE | COMMENTLINE)*
```

Rules are separated by one or more blank lines, and the first rule needs at
least one blank line before it; the newline that ends the `by` line is one
(`by` may not be followed by anything else on its line, or that text becomes a
`LINE` and the first rule is not preceded by a blank line, which is a parse
error). Comment lines (`%`) may appear anywhere inside a rule and are dropped.

**Lined rules.** The usual form:

```
    premise
    premise
    ---------------------- :: name
    conclusion
```

* The `LINELINE`'s *rest* (after the dashes) is parsed with the `metalang`
  lexer as `ident* '::' ident hom* EOF`: zero or more category names, the rule
  name, and homs (`------- S :: paren`, `------- :: pair {{ com pairing }}`).
  The rule's full name is the class prefix, then the definition prefix, then
  this name.
* The premise lines are the `LINE`s before the dashes, one premise per line.
  Each premise's text is first stripped of an optional trailing premise name
  `[[:name]]` (where `name` is a letter followed by letters and digits, and
  only trailing spaces may follow it); this names the premise for the Coq back
  end. If what remains, ignoring surrounding spaces, has the shape
  `{{ … }}`, the premise is *embedded prover code*: its interior is lexed as an
  embed body and each `[[ … ]]` inside it is a symbolic term. Otherwise the
  whole line is a symbolic term of the `formula` grammar.
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

* **Keywords are reserved in `metalang` and `bindspec` only.** `left`,
  `right`, `non`, `single`, `multiple`, `by`, `in`, `bind`, `names`, `union`
  cannot be nonterminal or metavariable names unless quoted at every use in
  those modes; in production elements and rule lines they are ordinary.
* **`%` comment at end of file** without a newline is a lexing error in
  `metalang`, accepted in `defnlang`.
* **Rule lines that start with a keyword.** A premise or conclusion whose first
  word is `fun`, `defn`, `grammar`, `embed`, `homs`, `metavar`, `indexvar`,
  `subrules`, `contextrules`, `substitutions`, `freevars`, `parsing`, `defns`,
  `funs`, `begincoqsection`, `endcoqsection` or `coqvariable` ends the
  definition. There is no escape.
* **Dashed lines are recognised anywhere** in `defnlang`: a line beginning
  with four or more `-` (after whitespace) is always a `LINELINE`, so a premise
  cannot begin with `----`.
* **`{{ com` at a line start inside a definition** is a comment block even if
  it was meant as the start of a premise.
* **`by` must end its line.** See §4.
* **Hom names need a following blank.** `{{com}}` is a parse error.
* **`>>` inside a definition** starts a block comment only when it is alone on
  its line (whitespace around it); mid-line `>>` is part of a `LINE`.
* **Nested `{{` inside a hom** lexes as a token the grammar does not accept.
  Braces that are needed in hom text must be single (`\mathit{[[x]]}` is fine
  because `{` and `}` are one-character strings).
* **`''` is an identifier**, the empty one; it is how a rule declares "no
  prefix".
* **Interstitials.** Ott discards whitespace and comments in `metalang`,
  `elements`, `bindspec` and `comp_bound` before the parser sees them;
  positions in error messages come from the lexer's line counter.

## 7. The lossless tree

haskott's parser builds a lossless tree (graft green tree; see the decision
"one graft green tree for Ott source and symbolic terms" in the project's
Hindsight bank) directly from the rules above, and the checked specification
is a projection of it. The tree holds every character of the input:

* Every interstitial of §2 is a trivia token: `Space` (a run of `nnws`),
  `Newline`, `LineComment` (`%` to end of line, newline excluded), and
  `BlockComment` (from `>>` to its matching `<<`, nesting included, as one
  token).
* `BLANKS` in hom bodies are kept as the same trivia kinds; the hom body's
  `string` runs are `HomText` tokens; `[[` and `]]` are tokens.
* In `defnlang`, a `LINE` is a `Line` token without its terminator, the
  terminator is a `Newline`, a `BLANKLINE` is `Space`? `Newline`, a
  `COMMENTLINE` is `Space`? `LineComment` `Newline`, and a `LINELINE` is a
  `Dashes` token followed by the tokens of its annotation lexed in `metalang`.
* Placement follows latti-parsing's rules: a node spans from its first to its
  last syntax token; an item (metavar declaration, rule, production, defn,
  rule in a body, clause) also owns the whitespace directly in front of it on
  its line and the trivia to the end of its last line; all other trivia belongs
  to the innermost node whose span contains it, so comment lines between two
  productions are siblings in the rule node; comment lines after the last
  production of a rule, indented past the rule's first column, stay with the
  rule (Rule 2). No node is given the comment lines above it.
* Node shapes: a `Premise`, `Conclusion`, `Formula` or `Clause` is
  `Space? Line`; a `RuleLine` is `Space? Dashes` followed by the annotation's
  tokens; a `DefnCom` is `Space? HomOpen Space? HomText("com")` followed by
  the body's tokens. `Name`, `Bindspec`, `Mse`, `CompBound`, `Hom` and
  `HomRef` are tight on both sides: the trivia around them belongs to their
  parent.
* In a definition body the comment lines that follow a rule, with or without
  blank lines between, are placed by Rule 2 like everywhere else: those
  indented past the rule's first line stay with the rule, the others belong
  to the definition. Ott's grammar makes a comment line directly after the
  conclusion part of the same block, but the tree does not record blocks.
* Rendering an unedited tree yields the input exactly. This is checked on
  every file of §8.

The *stage two* parse replaces each `Line` token of a premise, conclusion or
clause by a subtree whose rendering is the line's text, so after stage two the
law still holds for the whole file.

## 8. Corpus

Ott's repository ships 125 `.ott` files under `tests/` and 39 under
`examples/`, and the report's formalisation has `ott/expressions.ott`. All three are
the acceptance corpus: a file is accepted by haskott if and only if Ott 0.34
(fork) accepts it, and for accepted files the number of rules, productions and
definitions agree. Construct usage across `tests/` and `examples/` (files
containing it), measured 2026-10-17:

| construct | files | | construct | files |
|---|---|---|---|---|
| `grammar` | 167 | | `embed` | 41 |
| `metavar` | 110 | | `freevars` | 26 |
| `defn` | 114 | | `>>` block comments | 21 |
| `defns` | 106 | | `parsing` | 15 |
| `fun` (as a word) | 105 | | `</` comprehensions | 13 |
| `indexvar` | 67 | | `homs` sections | 10 |
| `(+` bindspecs | 67 | | `....` | 10 |
| `subrules` / `<::` | 63 / 62 | | `_::` | 10 |
| `substitutions` | 62 | | `funs` | 2 |
| quoted identifiers | 126 | | `names(` | 2 (commented out) |
| `...` | 36 | | `contextrules` | 0 (manual only) |
| | | | `begincoqsection` etc. | 0 |

Production categories seen: `M` (162 productions), `I` (47), `S` (39), `L`
(31), `JT` (27), `M I` (18), `L I` (15), `J` (7).
