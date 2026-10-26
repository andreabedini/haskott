{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeFamilies #-}

-- | Typed views over the lossless tree.
--
-- Each view is a newtype around a graft 'Cursor' focused on a node of one
-- kind (GRAMMAR.md §3, §4, §7), with accessors that read its parts. The
-- views do not validate: a malformed subtree casts, and its accessors
-- return what is there. "Haskott.Raw" projects these views into plain data.
module Haskott.Syntax.Ast
  ( -- * Cursors and helpers
    C
  , documentCursor
  , identValue
  , tokenValue

    -- * Items
  , Item (..)
  , castItem
  , Document (..)
  , documentItems

    -- * Declarations
  , MetavarDecl (..)
  , metavarKeyword
  , metavarNames
  , metavarHoms
  , Name (..)
  , nameIdent
  , nameHoms
  , GrammarSection (..)
  , grammarRules
  , Rule (..)
  , ruleNames
  , rulePrefix
  , ruleHoms
  , ruleProds
  , Prod (..)
  , prodElements
  , prodCategories
  , prodName
  , prodBindspecs
  , prodHoms
  , Elem (..)
  , elementsOf
  , Comp (..)
  , compElements
  , compIndex
  , compBound
  , CompBound (..)
  , boundTokens
  , Bindspecs (..)
  , bindspecsOf
  , Bindspec (..)
  , bindspecTokens
  , Mse (..)
  , mseParts
  , MsePart (..)
  , Hom (..)
  , homName
  , homBody
  , HomPart (..)
  , HomRef (..)
  , homRefParts
  , RefPart (..)
  , Embed (..)
  , embedName
  , embedBody
  , SubrulesSection (..)
  , subrulesOf
  , Subrule (..)
  , subruleIdents
  , subruleHoms
  , ContextrulesSection (..)
  , contextrulesOf
  , Contextrule (..)
  , contextruleIdents
  , SubstitutionsSection (..)
  , substitutionsOf
  , Substitution (..)
  , substitutionKind
  , substitutionIdents
  , substitutionHoms
  , FreevarsSection (..)
  , freevarsOf
  , Freevar (..)
  , freevarIdents
  , freevarHoms
  , EmbedSection (..)
  , embedsOf
  , ParsingSection (..)
  , parsingAnnotations
  , ParsingAnnotation (..)
  , parsingIdents
  , parsingOperator
  , HomsSection (..)
  , homsSectionWrapper
  , homsSectionItems
  , HomsItem (..)
  , homsItemName
  , homsItemBindspecs
  , homsItemHoms
  , CoqSection (..)
  , coqSectionKeyword
  , coqSectionName
  , CoqVariable (..)
  , coqVariableName

    -- * Definitions
  , Defns (..)
  , defnsName
  , defnsWrapper
  , defnsHoms
  , defnsDefns
  , Defn (..)
  , defnElements
  , defnCategories
  , defnName
  , defnWrapper
  , defnHoms
  , defnBodyItems
  , BodyItem (..)
  , castBodyItem
  , DRule (..)
  , drulePremises
  , druleRuleLine
  , druleConclusions
  , RuleLine (..)
  , ruleLineDashes
  , ruleLineAnnotation
  , ruleLineCategories
  , ruleLineName
  , ruleLineHoms
  , LineNode (..)
  , lineIndent
  , lineText
  , Lineless (..)
  , linelessFormulas
  , DefnCom (..)
  , defnComBody
  , Funs (..)
  , funsName
  , funsHoms
  , funsDefns
  , Fundefn (..)
  , fundefnElements
  , fundefnResult
  , fundefnName
  , fundefnHoms
  , fundefnClauses
  ) where

import Data.Maybe (listToMaybe, mapMaybe)
import Data.Text (Text)
import qualified Data.Text as T
import Graft
import qualified Graft.Ast as Ast
import qualified Graft.Cursor as Cursor
import qualified Graft.Green as Green
import Haskott.Syntax.Kind (Kind)
import qualified Haskott.Syntax.Kind as K

type C = Cursor Kind

-- | A cursor on the root of a parsed document.
documentCursor :: GreenNode Kind -> C
documentCursor = Cursor.fromGreen . Node

-- | The dequoted value of a @maybe_quoted_ident@ or an element (GRAMMAR.md
-- §2.2): @'t_'@ is @t_@, @''@ is empty, anything else is itself.
identValue :: Text -> Text
identValue s
  | T.length s >= 2 && T.head s == '\'' && T.last s == '\'' = T.init (T.tail s)
  | otherwise = s

-- | The text of a token cursor, or empty for a node.
tokenValue :: C -> Text
tokenValue c = case Cursor.green c of
  Token t -> Green.text t
  Node _ -> ""

kindIs :: Kind -> C -> Bool
kindIs k c = Cursor.kind c == k

children :: C -> [C]
children = Cursor.children

nodes :: Kind -> C -> [C]
nodes k = filter (kindIs k) . children

tokens :: Kind -> C -> [C]
tokens k = filter (kindIs k) . children

-- | Child idents, dequoted, in order.
idents :: C -> [Text]
idents = map (identValue . tokenValue) . tokens K.Ident

keywordText :: C -> Text
keywordText c = maybe "" tokenValue (listToMaybe (tokens K.Keyword c))

-- | Children split at the @::@ tokens: the segments between them.
segments :: C -> [[C]]
segments c = go (children c)
  where
    go cs = case break (kindIs K.ColonColon) cs of
      (seg, []) -> [seg]
      (seg, _ : more) -> seg : go more

segment :: Int -> C -> [C]
segment i c = case drop i (segments c) of
  (s : _) -> s
  [] -> []

identsIn :: [C] -> [Text]
identsIn = map (identValue . tokenValue) . filter (kindIs K.Ident)

view :: Kind -> (C -> a) -> C -> Maybe a
view k = Ast.matchNode (== k)

------------------------------------------------------------------------
-- Items

newtype Document = Document C

instance AstView Document where
  type AstViewKind Document = Kind
  fromCursor = view K.Document Document
  toCursor (Document c) = c

instance AstNode Document

data Item
  = ItemMetavar MetavarDecl
  | ItemGrammar GrammarSection
  | ItemSubrules SubrulesSection
  | ItemContextrules ContextrulesSection
  | ItemSubstitutions SubstitutionsSection
  | ItemFreevars FreevarsSection
  | ItemEmbed EmbedSection
  | ItemParsing ParsingSection
  | ItemHoms HomsSection
  | ItemDefns Defns
  | ItemFuns Funs
  | ItemCoqSection CoqSection
  | ItemCoqVariable CoqVariable

castItem :: C -> Maybe Item
castItem c = case Cursor.kind c of
  K.MetavarDecl -> Just (ItemMetavar (MetavarDecl c))
  K.GrammarSection -> Just (ItemGrammar (GrammarSection c))
  K.SubrulesSection -> Just (ItemSubrules (SubrulesSection c))
  K.ContextrulesSection -> Just (ItemContextrules (ContextrulesSection c))
  K.SubstitutionsSection -> Just (ItemSubstitutions (SubstitutionsSection c))
  K.FreevarsSection -> Just (ItemFreevars (FreevarsSection c))
  K.EmbedSection -> Just (ItemEmbed (EmbedSection c))
  K.ParsingSection -> Just (ItemParsing (ParsingSection c))
  K.HomsSection -> Just (ItemHoms (HomsSection c))
  K.Defns -> Just (ItemDefns (Defns c))
  K.Funs -> Just (ItemFuns (Funs c))
  K.CoqSection -> Just (ItemCoqSection (CoqSection c))
  K.CoqVariable -> Just (ItemCoqVariable (CoqVariable c))
  _ -> Nothing

documentItems :: Document -> [Item]
documentItems (Document c) = mapMaybe castItem (children c)

------------------------------------------------------------------------
-- Declarations

newtype MetavarDecl = MetavarDecl C

instance AstView MetavarDecl where
  type AstViewKind MetavarDecl = Kind
  fromCursor = view K.MetavarDecl MetavarDecl
  toCursor (MetavarDecl c) = c

instance AstNode MetavarDecl

-- | @metavar@ or @indexvar@.
metavarKeyword :: MetavarDecl -> Text
metavarKeyword (MetavarDecl c) = keywordText c

metavarNames :: MetavarDecl -> [Name]
metavarNames (MetavarDecl c) = Ast.children c

-- | The homs after @::=@ (those of the names are in the names).
metavarHoms :: MetavarDecl -> [Hom]
metavarHoms (MetavarDecl c) = Ast.children c

newtype Name = Name C

instance AstView Name where
  type AstViewKind Name = Kind
  fromCursor = view K.Name Name
  toCursor (Name c) = c

instance AstNode Name

nameIdent :: Name -> Text
nameIdent (Name c) = maybe "" id (listToMaybe (idents c))

nameHoms :: Name -> [Hom]
nameHoms (Name c) = Ast.children c

newtype GrammarSection = GrammarSection C

instance AstView GrammarSection where
  type AstViewKind GrammarSection = Kind
  fromCursor = view K.GrammarSection GrammarSection
  toCursor (GrammarSection c) = c

instance AstNode GrammarSection

grammarRules :: GrammarSection -> [Rule]
grammarRules (GrammarSection c) = Ast.children c

newtype Rule = Rule C

instance AstView Rule where
  type AstViewKind Rule = Kind
  fromCursor = view K.Rule Rule
  toCursor (Rule c) = c

instance AstNode Rule

ruleNames :: Rule -> [Name]
ruleNames (Rule c) = Ast.children c

-- | The production-name prefix, dequoted.
rulePrefix :: Rule -> Text
rulePrefix (Rule c) = maybe "" id (listToMaybe (idents c))

ruleHoms :: Rule -> [Hom]
ruleHoms (Rule c) = Ast.children c

ruleProds :: Rule -> [Prod]
ruleProds (Rule c) = Ast.children c

newtype Prod = Prod C

instance AstView Prod where
  type AstViewKind Prod = Kind
  fromCursor = view K.Prod Prod
  toCursor (Prod c) = c

instance AstNode Prod

-- | An element of a production or judgement form.
data Elem
  = ElemString Text Bool
  -- ^ the dequoted string and whether it was quoted
  | ElemDots Int
  -- ^ 0, 1 or 2 for @..@, @...@, @....@
  | ElemComp Comp

elementsOf :: [C] -> [Elem]
elementsOf = mapMaybe element
  where
    element c = case Cursor.kind c of
      K.Element -> Just (ElemString (identValue (tokenValue c)) False)
      K.QuotedElement -> Just (ElemString (identValue (tokenValue c)) True)
      K.Dots -> Just (ElemDots (T.length (tokenValue c) - 2))
      K.Comp -> Just (ElemComp (Comp c))
      _ -> Nothing

prodElements :: Prod -> [Elem]
prodElements (Prod c) = elementsOf (segment 0 c)

prodCategories :: Prod -> [Text]
prodCategories (Prod c) = identsIn (segment 1 c)

prodName :: Prod -> Text
prodName (Prod c) = maybe "" id (listToMaybe (identsIn (segment 2 c)))

prodBindspecs :: Prod -> [Bindspecs]
prodBindspecs (Prod c) = Ast.children c

prodHoms :: Prod -> [Hom]
prodHoms (Prod c) = Ast.children c

newtype Comp = Comp C

instance AstView Comp where
  type AstViewKind Comp = Kind
  fromCursor = view K.Comp Comp
  toCursor (Comp c) = c

instance AstNode Comp

compSegments :: C -> [[C]]
compSegments c = go (children c)
  where
    go cs = case break (kindIs K.CompMiddle) cs of
      (seg, []) -> [seg]
      (seg, _ : more) -> seg : go more

compElements :: Comp -> [Elem]
compElements (Comp c) = case compSegments c of
  (s : _) -> elementsOf s
  [] -> []

-- | The index between two @//@, when the comprehension has one.
compIndex :: Comp -> Maybe Text
compIndex (Comp c) = case compSegments c of
  (_ : mid : _ : _) -> listToMaybe [identValue (tokenValue t) | t <- mid, kindIs K.Element t]
  _ -> Nothing

compBound :: Comp -> Maybe CompBound
compBound (Comp c) = Ast.child c

newtype CompBound = CompBound C

instance AstView CompBound where
  type AstViewKind CompBound = Kind
  fromCursor = view K.CompBound CompBound
  toCursor (CompBound c) = c

instance AstNode CompBound

-- | The bound's tokens in order, with trivia left out: identifiers and
-- elements dequoted, @IN@ and the dots as written.
boundTokens :: CompBound -> [(Kind, Text)]
boundTokens (CompBound c) =
  [ (k, if k == K.Ident || k == K.Element then identValue (tokenValue t) else tokenValue t)
  | t <- children c
  , let k = Cursor.kind t
  , not (K.isTrivia k)
  ]

newtype Bindspecs = Bindspecs C

instance AstView Bindspecs where
  type AstViewKind Bindspecs = Kind
  fromCursor = view K.Bindspecs Bindspecs
  toCursor (Bindspecs c) = c

instance AstNode Bindspecs

bindspecsOf :: Bindspecs -> [Bindspec]
bindspecsOf (Bindspecs c) = Ast.children c

newtype Bindspec = Bindspec C

instance AstView Bindspec where
  type AstViewKind Bindspec = Kind
  fromCursor = view K.Bindspec Bindspec
  toCursor (Bindspec c) = c

instance AstNode Bindspec

-- | The non-trivia children in order: tokens as (kind, dequoted text) and
-- 'Mse' nodes.
bindspecTokens :: Bindspec -> [Either (Kind, Text) Mse]
bindspecTokens (Bindspec c) = mapMaybe part (children c)
  where
    part t
      | kindIs K.Mse t = Just (Right (Mse t))
      | K.isTrivia (Cursor.kind t) = Nothing
      | otherwise = Just (Left (Cursor.kind t, identValue (tokenValue t)))

newtype Mse = Mse C

instance AstView Mse where
  type AstViewKind Mse = Kind
  fromCursor = view K.Mse Mse
  toCursor (Mse c) = c

instance AstNode Mse

data MsePart
  = MseTok Kind Text
  | MseSub Mse
  | MseBound CompBound

mseParts :: Mse -> [MsePart]
mseParts (Mse c) = mapMaybe part (children c)
  where
    part t = case Cursor.kind t of
      K.Mse -> Just (MseSub (Mse t))
      K.CompBound -> Just (MseBound (CompBound t))
      k
        | K.isTrivia k -> Nothing
        | otherwise -> Just (MseTok k (identValue (tokenValue t)))

newtype Hom = Hom C

instance AstView Hom where
  type AstViewKind Hom = Kind
  fromCursor = view K.Hom Hom
  toCursor (Hom c) = c

instance AstNode Hom

-- | The pieces of a hom or embed body after its name: text runs, blanks,
-- dots, and references.
data HomPart
  = PartText Text
  | PartBlanks Text
  | PartDots Int
  | PartRef HomRef

bodyParts :: [C] -> [HomPart]
bodyParts = mapMaybe part
  where
    part t = case Cursor.kind t of
      K.HomText -> Just (PartText (tokenValue t))
      K.Space -> Just (PartBlanks (tokenValue t))
      K.Newline -> Just (PartBlanks (tokenValue t))
      K.Dots -> Just (PartDots (T.length (tokenValue t) - 2))
      K.HomRef -> Just (PartRef (HomRef t))
      _ -> Nothing

-- | The children after the name token, up to the closing braces. Ott's
-- @hom_name@ rule consumes one blank after the name; @{{com@ has no such
-- rule.
afterName :: Bool -> C -> [C]
afterName dropBlank c = case break (kindIs K.HomText) (children c) of
  (_, _ : more) ->
    let more' = if dropBlank then drop 1 more else more
     in takeWhile (not . kindIs K.HomClose) more'
  (_, []) -> []

homName :: Hom -> Text
homName (Hom c) = maybe "" tokenValue (listToMaybe (tokens K.HomText c))

homBody :: Hom -> [HomPart]
homBody (Hom c) = bodyParts (afterName True c)

newtype HomRef = HomRef C

instance AstView HomRef where
  type AstViewKind HomRef = Kind
  fromCursor = view K.HomRef HomRef
  toCursor (HomRef c) = c

instance AstNode HomRef

data RefPart
  = RefText Text
  -- ^ an identifier (hom mode) or a comprehension string (comp mode)
  | RefBlanks Text
  | RefDots Int
  | RefCompOpen
  | RefCompMiddle
  | RefCompClose
  | RefBound CompBound

homRefParts :: HomRef -> [RefPart]
homRefParts (HomRef c) = mapMaybe part (children c)
  where
    part t = case Cursor.kind t of
      K.HomText -> Just (RefText (tokenValue t))
      K.Element -> Just (RefText (tokenValue t))
      K.Space -> Just (RefBlanks (tokenValue t))
      K.Newline -> Just (RefBlanks (tokenValue t))
      K.Dots -> Just (RefDots (T.length (tokenValue t) - 2))
      K.CompOpen -> Just RefCompOpen
      K.CompMiddle -> Just RefCompMiddle
      K.CompClose -> Just RefCompClose
      K.CompBound -> Just (RefBound (CompBound t))
      _ -> Nothing

newtype Embed = Embed C

instance AstView Embed where
  type AstViewKind Embed = Kind
  fromCursor = view K.Embed Embed
  toCursor (Embed c) = c

instance AstNode Embed

embedName :: Embed -> Text
embedName (Embed c) = maybe "" tokenValue (listToMaybe (tokens K.HomText c))

embedBody :: Embed -> [HomPart]
embedBody (Embed c) = bodyParts (afterName True c)

newtype SubrulesSection = SubrulesSection C

instance AstView SubrulesSection where
  type AstViewKind SubrulesSection = Kind
  fromCursor = view K.SubrulesSection SubrulesSection
  toCursor (SubrulesSection c) = c

instance AstNode SubrulesSection

subrulesOf :: SubrulesSection -> [Subrule]
subrulesOf (SubrulesSection c) = Ast.children c

newtype Subrule = Subrule C

instance AstView Subrule where
  type AstViewKind Subrule = Kind
  fromCursor = view K.Subrule Subrule
  toCursor (Subrule c) = c

instance AstNode Subrule

-- | Lower root, upper root.
subruleIdents :: Subrule -> [Text]
subruleIdents (Subrule c) = idents c

subruleHoms :: Subrule -> [Hom]
subruleHoms (Subrule c) = Ast.children c

newtype ContextrulesSection = ContextrulesSection C

instance AstView ContextrulesSection where
  type AstViewKind ContextrulesSection = Kind
  fromCursor = view K.ContextrulesSection ContextrulesSection
  toCursor (ContextrulesSection c) = c

instance AstNode ContextrulesSection

contextrulesOf :: ContextrulesSection -> [Contextrule]
contextrulesOf (ContextrulesSection c) = Ast.children c

newtype Contextrule = Contextrule C

instance AstView Contextrule where
  type AstViewKind Contextrule = Kind
  fromCursor = view K.Contextrule Contextrule
  toCursor (Contextrule c) = c

instance AstNode Contextrule

-- | Context root, target root, hole root.
contextruleIdents :: Contextrule -> [Text]
contextruleIdents (Contextrule c) = idents c

newtype SubstitutionsSection = SubstitutionsSection C

instance AstView SubstitutionsSection where
  type AstViewKind SubstitutionsSection = Kind
  fromCursor = view K.SubstitutionsSection SubstitutionsSection
  toCursor (SubstitutionsSection c) = c

instance AstNode SubstitutionsSection

substitutionsOf :: SubstitutionsSection -> [Substitution]
substitutionsOf (SubstitutionsSection c) = Ast.children c

newtype Substitution = Substitution C

instance AstView Substitution where
  type AstViewKind Substitution = Kind
  fromCursor = view K.Substitution Substitution
  toCursor (Substitution c) = c

instance AstNode Substitution

-- | @single@ or @multiple@.
substitutionKind :: Substitution -> Text
substitutionKind (Substitution c) = keywordText c

-- | This root, that root, function name.
substitutionIdents :: Substitution -> [Text]
substitutionIdents (Substitution c) = idents c

substitutionHoms :: Substitution -> [Hom]
substitutionHoms (Substitution c) = Ast.children c

newtype FreevarsSection = FreevarsSection C

instance AstView FreevarsSection where
  type AstViewKind FreevarsSection = Kind
  fromCursor = view K.FreevarsSection FreevarsSection
  toCursor (FreevarsSection c) = c

instance AstNode FreevarsSection

freevarsOf :: FreevarsSection -> [Freevar]
freevarsOf (FreevarsSection c) = Ast.children c

newtype Freevar = Freevar C

instance AstView Freevar where
  type AstViewKind Freevar = Kind
  fromCursor = view K.Freevar Freevar
  toCursor (Freevar c) = c

instance AstNode Freevar

-- | This root, that root, function name.
freevarIdents :: Freevar -> [Text]
freevarIdents (Freevar c) = idents c

freevarHoms :: Freevar -> [Hom]
freevarHoms (Freevar c) = Ast.children c

newtype EmbedSection = EmbedSection C

instance AstView EmbedSection where
  type AstViewKind EmbedSection = Kind
  fromCursor = view K.EmbedSection EmbedSection
  toCursor (EmbedSection c) = c

instance AstNode EmbedSection

embedsOf :: EmbedSection -> [Embed]
embedsOf (EmbedSection c) = Ast.children c

newtype ParsingSection = ParsingSection C

instance AstView ParsingSection where
  type AstViewKind ParsingSection = Kind
  fromCursor = view K.ParsingSection ParsingSection
  toCursor (ParsingSection c) = c

instance AstNode ParsingSection

parsingAnnotations :: ParsingSection -> [ParsingAnnotation]
parsingAnnotations (ParsingSection c) = Ast.children c

newtype ParsingAnnotation = ParsingAnnotation C

instance AstView ParsingAnnotation where
  type AstViewKind ParsingAnnotation = Kind
  fromCursor = view K.ParsingAnnotation ParsingAnnotation
  toCursor (ParsingAnnotation c) = c

instance AstNode ParsingAnnotation

parsingIdents :: ParsingAnnotation -> [Text]
parsingIdents (ParsingAnnotation c) = idents c

-- | @<=@, @left@, @right@ or @non@.
parsingOperator :: ParsingAnnotation -> Text
parsingOperator (ParsingAnnotation c) =
  maybe "" tokenValue (listToMaybe (filter (\t -> kindIs K.LtEq t || kindIs K.Keyword t) (children c)))

newtype HomsSection = HomsSection C

instance AstView HomsSection where
  type AstViewKind HomsSection = Kind
  fromCursor = view K.HomsSection HomsSection
  toCursor (HomsSection c) = c

instance AstNode HomsSection

homsSectionWrapper :: HomsSection -> Text
homsSectionWrapper (HomsSection c) = maybe "" id (listToMaybe (idents c))

homsSectionItems :: HomsSection -> [HomsItem]
homsSectionItems (HomsSection c) = Ast.children c

newtype HomsItem = HomsItem C

instance AstView HomsItem where
  type AstViewKind HomsItem = Kind
  fromCursor = view K.HomsItem HomsItem
  toCursor (HomsItem c) = c

instance AstNode HomsItem

homsItemName :: HomsItem -> Text
homsItemName (HomsItem c) = maybe "" id (listToMaybe (idents c))

homsItemBindspecs :: HomsItem -> [Bindspecs]
homsItemBindspecs (HomsItem c) = Ast.children c

homsItemHoms :: HomsItem -> [Hom]
homsItemHoms (HomsItem c) = Ast.children c

newtype CoqSection = CoqSection C

instance AstView CoqSection where
  type AstViewKind CoqSection = Kind
  fromCursor = view K.CoqSection CoqSection
  toCursor (CoqSection c) = c

instance AstNode CoqSection

coqSectionKeyword :: CoqSection -> Text
coqSectionKeyword (CoqSection c) = keywordText c

coqSectionName :: CoqSection -> Text
coqSectionName (CoqSection c) = maybe "" id (listToMaybe (idents c))

newtype CoqVariable = CoqVariable C

instance AstView CoqVariable where
  type AstViewKind CoqVariable = Kind
  fromCursor = view K.CoqVariable CoqVariable
  toCursor (CoqVariable c) = c

instance AstNode CoqVariable

coqVariableName :: CoqVariable -> Text
coqVariableName (CoqVariable c) = maybe "" id (listToMaybe (idents c))

------------------------------------------------------------------------
-- Definitions

newtype Defns = Defns C

instance AstView Defns where
  type AstViewKind Defns = Kind
  fromCursor = view K.Defns Defns
  toCursor (Defns c) = c

instance AstNode Defns

defnsName :: Defns -> Text
defnsName (Defns c) = maybe "" id (listToMaybe (idents c))

defnsWrapper :: Defns -> Text
defnsWrapper (Defns c) = maybe "" id (listToMaybe (drop 1 (idents c)))

defnsHoms :: Defns -> [Hom]
defnsHoms (Defns c) = Ast.children c

defnsDefns :: Defns -> [Defn]
defnsDefns (Defns c) = Ast.children c

newtype Defn = Defn C

instance AstView Defn where
  type AstViewKind Defn = Kind
  fromCursor = view K.Defn Defn
  toCursor (Defn c) = c

instance AstNode Defn

defnElements :: Defn -> [Elem]
defnElements (Defn c) = elementsOf (segment 0 c)

defnCategories :: Defn -> [Text]
defnCategories (Defn c) = identsIn (segment 1 c)

defnName :: Defn -> Text
defnName (Defn c) = maybe "" id (listToMaybe (identsIn (segment 2 c)))

defnWrapper :: Defn -> Text
defnWrapper (Defn c) = maybe "" id (listToMaybe (identsIn (segment 3 c)))

defnHoms :: Defn -> [Hom]
defnHoms (Defn c) = Ast.children c

data BodyItem
  = BodyRule DRule
  | BodyLineless Lineless
  | BodyDefnCom DefnCom

defnBodyItems :: Defn -> [BodyItem]
defnBodyItems (Defn c) = mapMaybe castBodyItem (children c)

castBodyItem :: C -> Maybe BodyItem
castBodyItem t = case Cursor.kind t of
  K.DRule -> Just (BodyRule (DRule t))
  K.Lineless -> Just (BodyLineless (Lineless t))
  K.DefnCom -> Just (BodyDefnCom (DefnCom t))
  _ -> Nothing

newtype DRule = DRule C

instance AstView DRule where
  type AstViewKind DRule = Kind
  fromCursor = view K.DRule DRule
  toCursor (DRule c) = c

instance AstNode DRule

drulePremises :: DRule -> [LineNode]
drulePremises (DRule c) = map LineNode (nodes K.Premise c)

druleRuleLine :: DRule -> Maybe RuleLine
druleRuleLine (DRule c) = Ast.child c

druleConclusions :: DRule -> [LineNode]
druleConclusions (DRule c) = map LineNode (nodes K.Conclusion c)

newtype RuleLine = RuleLine C

instance AstView RuleLine where
  type AstViewKind RuleLine = Kind
  fromCursor = view K.RuleLine RuleLine
  toCursor (RuleLine c) = c

instance AstNode RuleLine

ruleLineDashes :: RuleLine -> Text
ruleLineDashes (RuleLine c) = maybe "" tokenValue (listToMaybe (tokens K.Dashes c))

-- | The text after the dashes, exactly as written.
ruleLineAnnotation :: RuleLine -> Text
ruleLineAnnotation (RuleLine c) = case break (kindIs K.Dashes) (children c) of
  (_, _ : more) -> T.concat (map (Green.render . Cursor.green) more)
  (_, []) -> ""

ruleLineCategories :: RuleLine -> [Text]
ruleLineCategories (RuleLine c) = identsIn (segment 0 c)

ruleLineName :: RuleLine -> Text
ruleLineName (RuleLine c) = maybe "" id (listToMaybe (identsIn (segment 1 c)))

ruleLineHoms :: RuleLine -> [Hom]
ruleLineHoms (RuleLine c) = Ast.children c

-- | A 'Premise', 'Conclusion', 'Formula' or 'Clause' node.
newtype LineNode = LineNode C

instance AstView LineNode where
  type AstViewKind LineNode = Kind
  fromCursor = Ast.matchNode (`elem` [K.Premise, K.Conclusion, K.Formula, K.Clause]) LineNode
  toCursor (LineNode c) = c

instance AstNode LineNode

lineIndent :: LineNode -> Text
lineIndent (LineNode c) = maybe "" tokenValue (listToMaybe (tokens K.Space c))

lineText :: LineNode -> Text
lineText (LineNode c) = maybe "" tokenValue (listToMaybe (tokens K.Line c))

newtype Lineless = Lineless C

instance AstView Lineless where
  type AstViewKind Lineless = Kind
  fromCursor = view K.Lineless Lineless
  toCursor (Lineless c) = c

instance AstNode Lineless

linelessFormulas :: Lineless -> [LineNode]
linelessFormulas (Lineless c) = map LineNode (nodes K.Formula c)

newtype DefnCom = DefnCom C

instance AstView DefnCom where
  type AstViewKind DefnCom = Kind
  fromCursor = view K.DefnCom DefnCom
  toCursor (DefnCom c) = c

instance AstNode DefnCom

-- | The body after @com@.
defnComBody :: DefnCom -> [HomPart]
defnComBody (DefnCom c) = bodyParts (afterName False c)

newtype Funs = Funs C

instance AstView Funs where
  type AstViewKind Funs = Kind
  fromCursor = view K.Funs Funs
  toCursor (Funs c) = c

instance AstNode Funs

funsName :: Funs -> Text
funsName (Funs c) = maybe "" id (listToMaybe (idents c))

funsHoms :: Funs -> [Hom]
funsHoms (Funs c) = Ast.children c

funsDefns :: Funs -> [Fundefn]
funsDefns (Funs c) = Ast.children c

newtype Fundefn = Fundefn C

instance AstView Fundefn where
  type AstViewKind Fundefn = Kind
  fromCursor = view K.Fundefn Fundefn
  toCursor (Fundefn c) = c

instance AstNode Fundefn

fundefnElements :: Fundefn -> [Elem]
fundefnElements (Fundefn c) = elementsOf (segment 0 c)

fundefnResult :: Fundefn -> Text
fundefnResult (Fundefn c) = maybe "" id (listToMaybe (identsIn (segment 1 c)))

fundefnName :: Fundefn -> Text
fundefnName (Fundefn c) = maybe "" id (listToMaybe (identsIn (segment 2 c)))

fundefnHoms :: Fundefn -> [Hom]
fundefnHoms (Fundefn c) = Ast.children c

fundefnClauses :: Fundefn -> [LineNode]
fundefnClauses (Fundefn c) = map LineNode (nodes K.Clause c)
