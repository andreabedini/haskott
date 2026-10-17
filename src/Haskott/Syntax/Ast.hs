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

instance AstNode Document where
  type AstNodeKind Document = Kind
  castNode = view K.Document Document
  nodeSyntax (Document c) = c

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

instance AstNode MetavarDecl where
  type AstNodeKind MetavarDecl = Kind
  castNode = view K.MetavarDecl MetavarDecl
  nodeSyntax (MetavarDecl c) = c

-- | @metavar@ or @indexvar@.
metavarKeyword :: MetavarDecl -> Text
metavarKeyword (MetavarDecl c) = keywordText c

metavarNames :: MetavarDecl -> [Name]
metavarNames (MetavarDecl c) = Ast.children c

-- | The homs after @::=@ (those of the names are in the names).
metavarHoms :: MetavarDecl -> [Hom]
metavarHoms (MetavarDecl c) = Ast.children c

newtype Name = Name C

instance AstNode Name where
  type AstNodeKind Name = Kind
  castNode = view K.Name Name
  nodeSyntax (Name c) = c

nameIdent :: Name -> Text
nameIdent (Name c) = maybe "" id (listToMaybe (idents c))

nameHoms :: Name -> [Hom]
nameHoms (Name c) = Ast.children c

newtype GrammarSection = GrammarSection C

instance AstNode GrammarSection where
  type AstNodeKind GrammarSection = Kind
  castNode = view K.GrammarSection GrammarSection
  nodeSyntax (GrammarSection c) = c

grammarRules :: GrammarSection -> [Rule]
grammarRules (GrammarSection c) = Ast.children c

newtype Rule = Rule C

instance AstNode Rule where
  type AstNodeKind Rule = Kind
  castNode = view K.Rule Rule
  nodeSyntax (Rule c) = c

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

instance AstNode Prod where
  type AstNodeKind Prod = Kind
  castNode = view K.Prod Prod
  nodeSyntax (Prod c) = c

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

instance AstNode Comp where
  type AstNodeKind Comp = Kind
  castNode = view K.Comp Comp
  nodeSyntax (Comp c) = c

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

instance AstNode CompBound where
  type AstNodeKind CompBound = Kind
  castNode = view K.CompBound CompBound
  nodeSyntax (CompBound c) = c

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

instance AstNode Bindspecs where
  type AstNodeKind Bindspecs = Kind
  castNode = view K.Bindspecs Bindspecs
  nodeSyntax (Bindspecs c) = c

bindspecsOf :: Bindspecs -> [Bindspec]
bindspecsOf (Bindspecs c) = Ast.children c

newtype Bindspec = Bindspec C

instance AstNode Bindspec where
  type AstNodeKind Bindspec = Kind
  castNode = view K.Bindspec Bindspec
  nodeSyntax (Bindspec c) = c

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

instance AstNode Mse where
  type AstNodeKind Mse = Kind
  castNode = view K.Mse Mse
  nodeSyntax (Mse c) = c

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

instance AstNode Hom where
  type AstNodeKind Hom = Kind
  castNode = view K.Hom Hom
  nodeSyntax (Hom c) = c

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

instance AstNode HomRef where
  type AstNodeKind HomRef = Kind
  castNode = view K.HomRef HomRef
  nodeSyntax (HomRef c) = c

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

instance AstNode Embed where
  type AstNodeKind Embed = Kind
  castNode = view K.Embed Embed
  nodeSyntax (Embed c) = c

embedName :: Embed -> Text
embedName (Embed c) = maybe "" tokenValue (listToMaybe (tokens K.HomText c))

embedBody :: Embed -> [HomPart]
embedBody (Embed c) = bodyParts (afterName True c)

newtype SubrulesSection = SubrulesSection C

instance AstNode SubrulesSection where
  type AstNodeKind SubrulesSection = Kind
  castNode = view K.SubrulesSection SubrulesSection
  nodeSyntax (SubrulesSection c) = c

subrulesOf :: SubrulesSection -> [Subrule]
subrulesOf (SubrulesSection c) = Ast.children c

newtype Subrule = Subrule C

instance AstNode Subrule where
  type AstNodeKind Subrule = Kind
  castNode = view K.Subrule Subrule
  nodeSyntax (Subrule c) = c

-- | Lower root, upper root.
subruleIdents :: Subrule -> [Text]
subruleIdents (Subrule c) = idents c

subruleHoms :: Subrule -> [Hom]
subruleHoms (Subrule c) = Ast.children c

newtype ContextrulesSection = ContextrulesSection C

instance AstNode ContextrulesSection where
  type AstNodeKind ContextrulesSection = Kind
  castNode = view K.ContextrulesSection ContextrulesSection
  nodeSyntax (ContextrulesSection c) = c

contextrulesOf :: ContextrulesSection -> [Contextrule]
contextrulesOf (ContextrulesSection c) = Ast.children c

newtype Contextrule = Contextrule C

instance AstNode Contextrule where
  type AstNodeKind Contextrule = Kind
  castNode = view K.Contextrule Contextrule
  nodeSyntax (Contextrule c) = c

-- | Context root, target root, hole root.
contextruleIdents :: Contextrule -> [Text]
contextruleIdents (Contextrule c) = idents c

newtype SubstitutionsSection = SubstitutionsSection C

instance AstNode SubstitutionsSection where
  type AstNodeKind SubstitutionsSection = Kind
  castNode = view K.SubstitutionsSection SubstitutionsSection
  nodeSyntax (SubstitutionsSection c) = c

substitutionsOf :: SubstitutionsSection -> [Substitution]
substitutionsOf (SubstitutionsSection c) = Ast.children c

newtype Substitution = Substitution C

instance AstNode Substitution where
  type AstNodeKind Substitution = Kind
  castNode = view K.Substitution Substitution
  nodeSyntax (Substitution c) = c

-- | @single@ or @multiple@.
substitutionKind :: Substitution -> Text
substitutionKind (Substitution c) = keywordText c

-- | This root, that root, function name.
substitutionIdents :: Substitution -> [Text]
substitutionIdents (Substitution c) = idents c

substitutionHoms :: Substitution -> [Hom]
substitutionHoms (Substitution c) = Ast.children c

newtype FreevarsSection = FreevarsSection C

instance AstNode FreevarsSection where
  type AstNodeKind FreevarsSection = Kind
  castNode = view K.FreevarsSection FreevarsSection
  nodeSyntax (FreevarsSection c) = c

freevarsOf :: FreevarsSection -> [Freevar]
freevarsOf (FreevarsSection c) = Ast.children c

newtype Freevar = Freevar C

instance AstNode Freevar where
  type AstNodeKind Freevar = Kind
  castNode = view K.Freevar Freevar
  nodeSyntax (Freevar c) = c

-- | This root, that root, function name.
freevarIdents :: Freevar -> [Text]
freevarIdents (Freevar c) = idents c

freevarHoms :: Freevar -> [Hom]
freevarHoms (Freevar c) = Ast.children c

newtype EmbedSection = EmbedSection C

instance AstNode EmbedSection where
  type AstNodeKind EmbedSection = Kind
  castNode = view K.EmbedSection EmbedSection
  nodeSyntax (EmbedSection c) = c

embedsOf :: EmbedSection -> [Embed]
embedsOf (EmbedSection c) = Ast.children c

newtype ParsingSection = ParsingSection C

instance AstNode ParsingSection where
  type AstNodeKind ParsingSection = Kind
  castNode = view K.ParsingSection ParsingSection
  nodeSyntax (ParsingSection c) = c

parsingAnnotations :: ParsingSection -> [ParsingAnnotation]
parsingAnnotations (ParsingSection c) = Ast.children c

newtype ParsingAnnotation = ParsingAnnotation C

instance AstNode ParsingAnnotation where
  type AstNodeKind ParsingAnnotation = Kind
  castNode = view K.ParsingAnnotation ParsingAnnotation
  nodeSyntax (ParsingAnnotation c) = c

parsingIdents :: ParsingAnnotation -> [Text]
parsingIdents (ParsingAnnotation c) = idents c

-- | @<=@, @left@, @right@ or @non@.
parsingOperator :: ParsingAnnotation -> Text
parsingOperator (ParsingAnnotation c) =
  maybe "" tokenValue (listToMaybe (filter (\t -> kindIs K.LtEq t || kindIs K.Keyword t) (children c)))

newtype HomsSection = HomsSection C

instance AstNode HomsSection where
  type AstNodeKind HomsSection = Kind
  castNode = view K.HomsSection HomsSection
  nodeSyntax (HomsSection c) = c

homsSectionWrapper :: HomsSection -> Text
homsSectionWrapper (HomsSection c) = maybe "" id (listToMaybe (idents c))

homsSectionItems :: HomsSection -> [HomsItem]
homsSectionItems (HomsSection c) = Ast.children c

newtype HomsItem = HomsItem C

instance AstNode HomsItem where
  type AstNodeKind HomsItem = Kind
  castNode = view K.HomsItem HomsItem
  nodeSyntax (HomsItem c) = c

homsItemName :: HomsItem -> Text
homsItemName (HomsItem c) = maybe "" id (listToMaybe (idents c))

homsItemBindspecs :: HomsItem -> [Bindspecs]
homsItemBindspecs (HomsItem c) = Ast.children c

homsItemHoms :: HomsItem -> [Hom]
homsItemHoms (HomsItem c) = Ast.children c

newtype CoqSection = CoqSection C

instance AstNode CoqSection where
  type AstNodeKind CoqSection = Kind
  castNode = view K.CoqSection CoqSection
  nodeSyntax (CoqSection c) = c

coqSectionKeyword :: CoqSection -> Text
coqSectionKeyword (CoqSection c) = keywordText c

coqSectionName :: CoqSection -> Text
coqSectionName (CoqSection c) = maybe "" id (listToMaybe (idents c))

newtype CoqVariable = CoqVariable C

instance AstNode CoqVariable where
  type AstNodeKind CoqVariable = Kind
  castNode = view K.CoqVariable CoqVariable
  nodeSyntax (CoqVariable c) = c

coqVariableName :: CoqVariable -> Text
coqVariableName (CoqVariable c) = maybe "" id (listToMaybe (idents c))

------------------------------------------------------------------------
-- Definitions

newtype Defns = Defns C

instance AstNode Defns where
  type AstNodeKind Defns = Kind
  castNode = view K.Defns Defns
  nodeSyntax (Defns c) = c

defnsName :: Defns -> Text
defnsName (Defns c) = maybe "" id (listToMaybe (idents c))

defnsWrapper :: Defns -> Text
defnsWrapper (Defns c) = maybe "" id (listToMaybe (drop 1 (idents c)))

defnsHoms :: Defns -> [Hom]
defnsHoms (Defns c) = Ast.children c

defnsDefns :: Defns -> [Defn]
defnsDefns (Defns c) = Ast.children c

newtype Defn = Defn C

instance AstNode Defn where
  type AstNodeKind Defn = Kind
  castNode = view K.Defn Defn
  nodeSyntax (Defn c) = c

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

instance AstNode DRule where
  type AstNodeKind DRule = Kind
  castNode = view K.DRule DRule
  nodeSyntax (DRule c) = c

drulePremises :: DRule -> [LineNode]
drulePremises (DRule c) = map LineNode (nodes K.Premise c)

druleRuleLine :: DRule -> Maybe RuleLine
druleRuleLine (DRule c) = Ast.child c

druleConclusions :: DRule -> [LineNode]
druleConclusions (DRule c) = map LineNode (nodes K.Conclusion c)

newtype RuleLine = RuleLine C

instance AstNode RuleLine where
  type AstNodeKind RuleLine = Kind
  castNode = view K.RuleLine RuleLine
  nodeSyntax (RuleLine c) = c

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

instance AstNode LineNode where
  type AstNodeKind LineNode = Kind
  castNode = Ast.matchNode (`elem` [K.Premise, K.Conclusion, K.Formula, K.Clause]) LineNode
  nodeSyntax (LineNode c) = c

lineIndent :: LineNode -> Text
lineIndent (LineNode c) = maybe "" tokenValue (listToMaybe (tokens K.Space c))

lineText :: LineNode -> Text
lineText (LineNode c) = maybe "" tokenValue (listToMaybe (tokens K.Line c))

newtype Lineless = Lineless C

instance AstNode Lineless where
  type AstNodeKind Lineless = Kind
  castNode = view K.Lineless Lineless
  nodeSyntax (Lineless c) = c

linelessFormulas :: Lineless -> [LineNode]
linelessFormulas (Lineless c) = map LineNode (nodes K.Formula c)

newtype DefnCom = DefnCom C

instance AstNode DefnCom where
  type AstNodeKind DefnCom = Kind
  castNode = view K.DefnCom DefnCom
  nodeSyntax (DefnCom c) = c

-- | The body after @com@.
defnComBody :: DefnCom -> [HomPart]
defnComBody (DefnCom c) = bodyParts (afterName False c)

newtype Funs = Funs C

instance AstNode Funs where
  type AstNodeKind Funs = Kind
  castNode = view K.Funs Funs
  nodeSyntax (Funs c) = c

funsName :: Funs -> Text
funsName (Funs c) = maybe "" id (listToMaybe (idents c))

funsHoms :: Funs -> [Hom]
funsHoms (Funs c) = Ast.children c

funsDefns :: Funs -> [Fundefn]
funsDefns (Funs c) = Ast.children c

newtype Fundefn = Fundefn C

instance AstNode Fundefn where
  type AstNodeKind Fundefn = Kind
  castNode = view K.Fundefn Fundefn
  nodeSyntax (Fundefn c) = c

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
