-- | The syntax kinds of haskott's lossless tree.
--
-- One flat enumeration serves both tokens and nodes, as graft's @kind@
-- parameter. The constructors follow @GRAMMAR.md@: the trivia kinds of §7,
-- the token kinds of the lexer modes of §2, and one node kind per
-- syntactic construct of §3 and §4.
module Haskott.Syntax.Kind
  ( Kind (..)
  , isTrivia
  , isTokenKind
  ) where

import Data.Text (Text)

data Kind
  = -- Trivia (GRAMMAR.md §7)
    Space
    -- ^ a run of non-newline whitespace: space, tab, form feed
  | Newline
    -- ^ one line terminator: @\\n@, @\\r@ or @\\r\\n@
  | LineComment
    -- ^ from @%@ to the end of the line, terminator excluded
  | BlockComment
    -- ^ from @>>@ to its matching @<<@, nesting included

    -- Tokens of the @metalang@ and @bindspec@ modes (§2.4, §2.8)
  | Keyword
    -- ^ a reserved word; the token text is the spelling
  | Ident
    -- ^ a @maybe_quoted_ident@; the token text is the spelling, quotes
    -- included
  | Comma
  | ColonColonEq
    -- ^ @::=@
  | Bar
    -- ^ @|@
  | ColonColon
    -- ^ @::@
  | LtColonColon
    -- ^ @<::@
  | UnderscoreColonColon
    -- ^ @_::@
  | LtEq
    -- ^ @<=@
  | HomOpen
    -- ^ @{{@ or @{{*@
  | HomClose
    -- ^ @}}@ or @*}}@
  | BindOpen
    -- ^ @(+@
  | BindClose
    -- ^ @+)@
  | Eq
  | Hash
  | LParen
  | RParen
  | Empty
    -- ^ @{}@

    -- Tokens of the @elements@ and @comp_bound@ modes (§2.5, §2.7)
  | Element
    -- ^ a whitespace-delimited string in a production or judgement form
  | QuotedElement
    -- ^ an element whose spelling starts with @'@ and has at least two
    -- characters (§3.4)
  | Dots
    -- ^ @..@, @...@ or @....@
  | CompOpen
    -- ^ @</@
  | CompMiddle
    -- ^ @//@
  | CompClose
    -- ^ @/>@
  | CompIn
    -- ^ @IN@

    -- Tokens of the @hom@ modes (§2.6)
  | HomText
    -- ^ a run of hom body text between blanks, brackets, braces and dots
  | RefOpen
    -- ^ @[[@
  | RefClose
    -- ^ @]]@

    -- Tokens of the @defnlang@ mode (§2.9)
  | Line
    -- ^ a rule premise, conclusion, formula or function clause, as
    -- written, without its terminator and without its indentation
  | Dashes
    -- ^ the run of @-@ that starts a rule-name line

    -- Tokens of symbolic terms (stage two, §5)
  | TTerminal
    -- ^ a terminal of the user's grammar, or a disambiguation delimiter
  | TNonterm
    -- ^ a nonterminal: root and suffix as written
  | TMetavar
    -- ^ a metavariable: root and suffix as written, or @:name:text@
  | TVar
    -- ^ a concrete variable admitted by a @lex@ hom
  | TProdName
    -- ^ a @:prodname:@ or @:concrete:@ pseudo-terminal
  | TIndex
    -- ^ an index variable in a bound, possibly @-1@
  | TNumber
    -- ^ the lower bound of a comprehension
  | PremiseLabel
    -- ^ the @:name@ of a named premise

    -- Error recovery
  | Garbage
    -- ^ text skipped after a parse error, up to where parsing resumed

    -- Nodes (§3, §4). Every token kind is declared above: 'isTokenKind'
    -- relies on the order.
  | Document
  | MetavarDecl
    -- ^ @metavar@ or @indexvar@ declaration
  | Name
    -- ^ one name of a declaration or rule, with its own homs
  | GrammarSection
  | Rule
  | Prod
  | Comp
    -- ^ a @</ ... />@ list comprehension in a production
  | CompBound
    -- ^ the bound of a comprehension: @n@, @i IN n@, @i IN 1..n@
  | Bindspecs
    -- ^ one @(+ ... +)@ group
  | Bindspec
  | Mse
  | Hom
  | HomRef
    -- ^ @[[ ... ]]@ inside a hom, embed or comment block
  | EmbedSection
  | Embed
  | SubrulesSection
  | Subrule
  | ContextrulesSection
  | Contextrule
  | SubstitutionsSection
  | Substitution
  | FreevarsSection
  | Freevar
  | Defns
  | Defn
  | DRule
    -- ^ a rule with a dashed line
  | Premise
  | RuleLine
    -- ^ the dashed line with its annotation
  | Conclusion
  | Lineless
    -- ^ a block of lines with no dashed line (§4)
  | Formula
    -- ^ one line of a lineless rule
  | DefnCom
    -- ^ a @{{ com ... }}@ block among the rules of a definition
  | Funs
  | Fundefn
  | Clause
  | ParsingSection
  | ParsingAnnotation
  | HomsSection
  | HomsItem
  | CoqSection
  | CoqVariable

    -- Nodes of symbolic terms (stage two)
  | TNode Text Text
    -- ^ a production of the user's grammar: the rule's primary root and
    -- the production's name
  | TList
    -- ^ the elements of a list form, possibly none
  | TEntry
    -- ^ one entry of a list form
  | TListForm
    -- ^ a dot form or a comprehension in a list
  | PremiseName
    -- ^ the trailing @[[:name]]@ of a premise
  | EmbedPremise
    -- ^ a premise of embedded prover code with quoted terms
  | ErrorItem
    -- ^ an item that did not parse: its indentation and the skipped text
  deriving (Eq, Ord, Show)

-- | Whitespace and comments.
isTrivia :: Kind -> Bool
isTrivia k = case k of
  Space -> True
  Newline -> True
  LineComment -> True
  BlockComment -> True
  _ -> False

-- | Kinds that occur only on tokens: those declared before 'Document'.
isTokenKind :: Kind -> Bool
isTokenKind k = k < Document || k == PremiseLabel
