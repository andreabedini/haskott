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

Milestone 1, the specification of the Ott source language, is `GRAMMAR.md`.
Nothing is parsed yet.

## Building

haskott depends on a sibling checkout of graft. The layout is fixed:

```
<parent>/haskott   (this repository)
<parent>/graft     (a checkout of andreabedini/graft)
```

Toolchain: GHC 9.12.2 and cabal from ghcup.

```console
$ cabal build all
```

## Reference material

The acceptance corpus is Ott's own `tests/` and `examples/` directories and
`haskell-report-ott/ott/expressions.ott`, checked differentially against the
Ott binary. `ott-jfp.pdf` in this directory is the paper; it is not tracked.
