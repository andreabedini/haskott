-- | The raw specification: plain data projected from the typed views.
--
-- This mirrors what Ott's parser produces (its @Raw_*@ records) before any
-- checking: names are dequoted, homs are split into their pieces, rule
-- bodies are lines of text. "Haskott.Raw.Show" prints it in the format of
-- Ott's @-showraw@ option, which is how the projection is verified.
module Haskott.Raw
  ( Document
  , Item (..)
  , MetavarDefn (..)
  , Hom (..)
  , HomSpecEl (..)
  , Embed (..)
  , EmbedEl (..)
  , Rule (..)
  , Prod (..)
  , Element (..)
  , CompBound (..)
  , Bindspec (..)
  , Mse (..)
  , Subrule (..)
  , Contextrule (..)
  , Substitution (..)
  , Freevar (..)
  , ParsingAnnotation (..)
  , HomSection (..)
  , HomSectionItem (..)
  , DefnClass (..)
  , Defn (..)
  , SemirawRule (..)
  , RuleAnnot (..)
  , FunClass (..)
  , FunDefn (..)
  , rawDocument
  , mergeFragments
  ) where

import Data.Text (Text)
import qualified Data.Text as T
import Graft
import qualified Graft.Cursor as Cursor
import Haskott.Syntax.Ast hiding
  ( Bindspec, CompBound, Contextrule, Defn, Document, Embed, Freevar, Hom, Item (..), Mse
  , ParsingAnnotation, Prod, Rule, Subrule, Substitution
  , compBound, embedName, homName, prodBindspecs, prodCategories, prodElements, prodHoms
  , prodName, ruleHoms, ruleNames, rulePrefix, ruleProds
  )
import qualified Haskott.Syntax.Ast as A
import Haskott.Syntax.Kind (Kind)
import qualified Haskott.Syntax.Kind as K

type Document = [Item]

data Item
  = ItemMetavar MetavarDefn
  | ItemGrammar [Rule]
  | ItemSubrules [Subrule]
  | ItemContextrules [Contextrule]
  | ItemSubstitutions [Substitution]
  | ItemFreevars [Freevar]
  | ItemEmbed [Embed]
  | ItemParsing [ParsingAnnotation]
  | ItemHomSection HomSection
  | ItemDefns DefnClass
  | ItemFuns FunClass
  | ItemCoqSection Bool Text
  -- ^ begin?, name
  | ItemCoqVariable Text
  deriving (Eq, Show)

data MetavarDefn = MetavarDefn
  { mvdIndexvar :: Bool
  , mvdNames :: [(Text, [Hom])]
  , mvdHoms :: [Hom]
  , mvdRange :: TextRange
  }
  deriving (Eq, Show)

data Hom = Hom
  { homName :: Text
  , homSpec :: [HomSpecEl]
  , homRange :: TextRange
  }
  deriving (Eq, Show)

data HomSpecEl
  = HomString Text
  | HomBlanks Text
  | HomIdent [Text]
  -- ^ @[[ ... ]]@: identifiers and blanks, as Ott keeps them
  | HomIdentDots [Text] Int [Text]
  | HomIdentComp [Text] CompBound
  deriving (Eq, Show)

data Embed = Embed
  { embedName :: Text
  , embedSpec :: [EmbedEl]
  , embedRange :: TextRange
  }
  deriving (Eq, Show)

data EmbedEl
  = EmbedString Text
  | EmbedInner Text
  deriving (Eq, Show)

data Rule = Rule
  { ruleNames :: [(Text, [Hom])]
  , rulePrefix :: Text
  , ruleHoms :: [Hom]
  , ruleProds :: [Prod]
  , ruleRange :: TextRange
  }
  deriving (Eq, Show)

data Prod = Prod
  { prodElements :: [Element]
  , prodCategories :: [Text]
  , prodName :: Text
  , prodBindspecs :: [Bindspec]
  , prodHoms :: [Hom]
  , prodRange :: TextRange
  }
  deriving (Eq, Show)

data Element
  = EIdent Text
  | EQuoted Text
  | EDots Int
  | EComp [Element] (Maybe Text) CompBound
  deriving (Eq, Show)

data CompBound
  = Bound Text
  | BoundU Text Text
  | BoundLU Text Text Int Text
  deriving (Eq, Show)

data Bindspec
  = Bind Mse Text TextRange
  | AuxFnDef Text Mse TextRange
  | NamesEqual Mse Mse TextRange
  | NamesDistinct Mse Mse TextRange
  | AllNamesDistinct Mse TextRange
  deriving (Eq, Show)

data Mse
  = MseVar Text
  | MseDots Text Int Text
  | MseComp Text CompBound
  | MseAux Text Text
  | MseAuxDots Text Text Int Text
  | MseAuxComp Text Text CompBound
  | MseUnion Mse Mse
  | MseEmpty
  deriving (Eq, Show)

data Subrule = Subrule
  { srLower :: Text
  , srUpper :: Text
  , srHoms :: [Hom]
  , srRange :: TextRange
  }
  deriving (Eq, Show)

data Contextrule = Contextrule
  { crNtr :: Text
  , crTarget :: Text
  , crHole :: Text
  , crRange :: TextRange
  }
  deriving (Eq, Show)

data Substitution = Substitution
  { sbMultiple :: Bool
  , sbThis :: Text
  , sbThat :: Text
  , sbName :: Text
  , sbHoms :: [Hom]
  , sbRange :: TextRange
  }
  deriving (Eq, Show)

data Freevar = Freevar
  { fvThis :: Text
  , fvThat :: Text
  , fvName :: Text
  , fvHoms :: [Hom]
  , fvRange :: TextRange
  }
  deriving (Eq, Show)

data ParsingAnnotation = ParsingAnnotation
  { paLeft :: Text
  , paOperator :: Text
  , paRight :: Text
  , paRange :: TextRange
  }
  deriving (Eq, Show)

data HomSection = HomSection
  { hsWrapper :: Text
  , hsItems :: [HomSectionItem]
  , hsRange :: TextRange
  }
  deriving (Eq, Show)

data HomSectionItem = HomSectionItem
  { hsiName :: Text
  , hsiBindspecs :: [Bindspec]
  , hsiHoms :: [Hom]
  , hsiRange :: TextRange
  }
  deriving (Eq, Show)

data DefnClass = DefnClass
  { dcName :: Text
  , dcWrapper :: Text
  , dcHoms :: [Hom]
  , dcDefns :: [Defn]
  , dcRange :: TextRange
  }
  deriving (Eq, Show)

data Defn = Defn
  { dElements :: [Element]
  , dCategories :: [Text]
  , dName :: Text
  , dWrapper :: Text
  , dHoms :: [Hom]
  , dBody :: [SemirawRule]
  , dRange :: TextRange
  }
  deriving (Eq, Show)

-- | A rule as lines of text (GRAMMAR.md §4). Lines keep their indentation,
-- as Ott's @LINE@ token does.
data SemirawRule
  = LinedRule [Text] Text RuleAnnot [Text] TextRange
  -- ^ premises, the annotation after the dashes as written and parsed,
  -- conclusions
  | LinelessRule [Text] TextRange
  | DefnComRule [EmbedEl] TextRange
  deriving (Eq, Show)

-- | The annotation of a rule line: categories, name and homs.
data RuleAnnot = RuleAnnot
  { raCategories :: [Text]
  , raName :: Text
  , raHoms :: [Hom]
  }
  deriving (Eq, Show)

data FunClass = FunClass
  { fcName :: Text
  , fcHoms :: [Hom]
  , fcDefns :: [FunDefn]
  , fcRange :: TextRange
  }
  deriving (Eq, Show)

data FunDefn = FunDefn
  { fdElements :: [Element]
  , fdResult :: Text
  , fdName :: Text
  , fdHoms :: [Hom]
  , fdClauses :: [Text]
  , fdRange :: TextRange
  }
  deriving (Eq, Show)

------------------------------------------------------------------------
-- Projection

rawDocument :: GreenNode Kind -> Document
rawDocument tree = map item (documentItems (A.Document (documentCursor tree)))

item :: A.Item -> Item
item it = case it of
  A.ItemMetavar d ->
    ItemMetavar
      MetavarDefn
        { mvdIndexvar = metavarKeyword d == T.pack "indexvar"
        , mvdNames = map name (metavarNames d)
        , mvdHoms = map hom (metavarHoms d)
        , mvdRange = Cursor.range (nodeSyntax d)
        }
  A.ItemGrammar g -> ItemGrammar (map rule (grammarRules g))
  A.ItemSubrules s -> ItemSubrules (map subrule (subrulesOf s))
  A.ItemContextrules s -> ItemContextrules (map contextrule (contextrulesOf s))
  A.ItemSubstitutions s -> ItemSubstitutions (map substitution (substitutionsOf s))
  A.ItemFreevars s -> ItemFreevars (map freevar (freevarsOf s))
  A.ItemEmbed s -> ItemEmbed (map embed (embedsOf s))
  A.ItemParsing s -> ItemParsing (map parsingAnnotation (parsingAnnotations s))
  A.ItemHoms s ->
    ItemHomSection
      HomSection
        { hsWrapper = homsSectionWrapper s
        , hsItems = map homsItem (homsSectionItems s)
        , hsRange = Cursor.range (nodeSyntax s)
        }
  A.ItemDefns d ->
    ItemDefns
      DefnClass
        { dcName = defnsName d
        , dcWrapper = defnsWrapper d
        , dcHoms = map hom (defnsHoms d)
        , dcDefns = map defn (defnsDefns d)
        , dcRange = Cursor.range (nodeSyntax d)
        }
  A.ItemFuns f ->
    ItemFuns
      FunClass
        { fcName = funsName f
        , fcHoms = map hom (funsHoms f)
        , fcDefns = map fundefn (funsDefns f)
        , fcRange = Cursor.range (nodeSyntax f)
        }
  A.ItemCoqSection s -> ItemCoqSection (coqSectionKeyword s == T.pack "begincoqsection") (coqSectionName s)
  A.ItemCoqVariable v -> ItemCoqVariable (coqVariableName v)

name :: A.Name -> (Text, [Hom])
name n = (nameIdent n, map hom (nameHoms n))

hom :: A.Hom -> Hom
hom h = Hom {homName = A.homName h, homSpec = map homSpecEl (homBody h), homRange = Cursor.range (nodeSyntax h)}

homSpecEl :: HomPart -> HomSpecEl
homSpecEl p = case p of
  PartText t -> HomString t
  PartBlanks t -> HomBlanks t
  PartDots n -> HomString (dots n)
  PartRef r -> homInner (homRefParts r)

homInner :: [RefPart] -> HomSpecEl
homInner parts = case dropWhile isBlank parts of
  -- Ott lexes the spaces before </ as part of it, and in comp_bound mode
  -- blanks are not tokens.
  (RefCompOpen : more) ->
    let (strs, rest) = break isMiddle more
        bound = case dropWhile isBlank (drop 1 rest) of
          (RefBound b : _) -> compBoundOf b
          _ -> Bound T.empty
     in HomIdentComp [t | RefText t <- strs] bound
  _ -> case break isDots parts of
    (before, []) -> HomIdent (map textOf before)
    (before, RefDots n : after) -> HomIdentDots (map textOf before) n (map textOf after)
    (before, _ : after) -> HomIdent (map textOf (before ++ after))
  where
    isBlank x = case x of
      RefBlanks _ -> True
      _ -> False
    isMiddle x = case x of
      RefCompMiddle -> True
      _ -> False
    isDots x = case x of
      RefDots _ -> True
      _ -> False
    textOf x = case x of
      RefText t -> t
      RefBlanks t -> t
      _ -> T.empty

embed :: A.Embed -> Embed
embed e = Embed {embedName = A.embedName e, embedSpec = map embedEl (embedBody e), embedRange = Cursor.range (nodeSyntax e)}

embedEl :: HomPart -> EmbedEl
embedEl p = case p of
  PartText t -> EmbedString t
  PartBlanks t -> EmbedString t
  PartDots n -> EmbedString (dots n)
  PartRef r -> EmbedInner (T.concat [t | x <- homRefParts r, t <- textOf x])
  where
    textOf x = case x of
      RefText t -> [t]
      RefBlanks t -> [t]
      _ -> []

dots :: Int -> Text
dots n = T.replicate (n + 2) (T.pack ".")

rule :: A.Rule -> Rule
rule r =
  Rule
    { ruleNames = map name (A.ruleNames r)
    , rulePrefix = A.rulePrefix r
    , ruleHoms = map hom (A.ruleHoms r)
    , ruleProds = map prod (A.ruleProds r)
    , ruleRange = Cursor.range (nodeSyntax r)
    }

prod :: A.Prod -> Prod
prod p =
  Prod
    { prodElements = map element (A.prodElements p)
    , prodCategories = A.prodCategories p
    , prodName = A.prodName p
    , prodBindspecs = concatMap (map bindspec . bindspecsOf) (A.prodBindspecs p)
    , prodHoms = map hom (A.prodHoms p)
    , prodRange = Cursor.range (nodeSyntax p)
    }

element :: Elem -> Element
element e = case e of
  ElemString s False -> EIdent s
  ElemString s True -> EQuoted s
  ElemDots n -> EDots n
  ElemComp c ->
    EComp (map element (compElements c)) (compIndex c) (maybe (Bound T.empty) compBoundOf (A.compBound c))

compBoundOf :: A.CompBound -> CompBound
compBoundOf b = case boundTokens b of
  [(_, a)] -> Bound a
  [(_, a), (K.CompIn, _), (_, u)] -> BoundU a u
  [(_, a), (K.CompIn, _), (_, l), (K.Dots, d), (_, u)] -> BoundLU a l (T.length d - 2) u
  toks -> Bound (T.unwords (map snd toks))

bindspec :: A.Bindspec -> Bindspec
bindspec b =
  let range = Cursor.range (nodeSyntax b)
   in case bindspecTokens b of
        [Left (K.Keyword, _), Right m, Left (K.Keyword, _), Left (_, x)] -> Bind (mse m) x range
        [Left (_, f), Left (K.Eq, _), Right m] -> AuxFnDef f (mse m) range
        [Left (K.Keyword, _), Left (K.LParen, _), Right m, Left (K.RParen, _), Left (op, _), Left (K.Keyword, _), Left (K.LParen, _), Right m', Left (K.RParen, _)]
          | op == K.Eq -> NamesEqual (mse m) (mse m') range
          | otherwise -> NamesDistinct (mse m) (mse m') range
        [Left (K.Keyword, _), Left (K.LParen, _), Right m, Left (K.RParen, _)] -> AllNamesDistinct (mse m) range
        _ -> AllNamesDistinct MseEmpty range

mse :: A.Mse -> Mse
mse m = case mseParts m of
  [MseSub a, MseTok K.Keyword _, MseSub b] -> MseUnion (mse a) (mse b)
  [MseTok K.Empty _] -> MseEmpty
  [MseTok K.Ident x] -> MseVar x
  [MseTok K.Ident x, MseTok K.Dots d, MseTok K.Ident y] -> MseDots x (T.length d - 2) y
  [MseTok K.CompOpen _, MseTok K.Ident x, MseTok K.CompMiddle _, MseBound b, MseTok K.CompClose _] -> MseComp x (compBoundOf b)
  [MseTok K.Ident f, MseTok K.LParen _, MseTok K.Ident x, MseTok K.RParen _] -> MseAux f x
  [MseTok K.Ident f, MseTok K.LParen _, MseTok K.Ident x, MseTok K.Dots d, MseTok K.Ident y, MseTok K.RParen _] -> MseAuxDots f x (T.length d - 2) y
  [MseTok K.Ident f, MseTok K.LParen _, MseTok K.CompOpen _, MseTok K.Ident x, MseTok K.CompMiddle _, MseBound b, MseTok K.CompClose _, MseTok K.RParen _] -> MseAuxComp f x (compBoundOf b)
  [MseTok K.Ident f, MseTok K.CompOpen _, MseTok K.Ident x, MseTok K.CompMiddle _, MseBound b, MseTok K.CompClose _] -> MseAuxComp f x (compBoundOf b)
  _ -> MseEmpty

subrule :: A.Subrule -> Subrule
subrule s = case subruleIdents s of
  [lo, hi] -> Subrule lo hi (map hom (subruleHoms s)) (Cursor.range (nodeSyntax s))
  ids -> Subrule (headOr ids) (headOr (drop 1 ids)) (map hom (subruleHoms s)) (Cursor.range (nodeSyntax s))

contextrule :: A.Contextrule -> Contextrule
contextrule c =
  let ids = contextruleIdents c
   in Contextrule (headOr ids) (headOr (drop 1 ids)) (headOr (drop 2 ids)) (Cursor.range (nodeSyntax c))

substitution :: A.Substitution -> Substitution
substitution s =
  let ids = substitutionIdents s
   in Substitution
        { sbMultiple = substitutionKind s == T.pack "multiple"
        , sbThis = headOr ids
        , sbThat = headOr (drop 1 ids)
        , sbName = headOr (drop 2 ids)
        , sbHoms = map hom (substitutionHoms s)
        , sbRange = Cursor.range (nodeSyntax s)
        }

freevar :: A.Freevar -> Freevar
freevar f =
  let ids = freevarIdents f
   in Freevar
        { fvThis = headOr ids
        , fvThat = headOr (drop 1 ids)
        , fvName = headOr (drop 2 ids)
        , fvHoms = map hom (freevarHoms f)
        , fvRange = Cursor.range (nodeSyntax f)
        }

parsingAnnotation :: A.ParsingAnnotation -> ParsingAnnotation
parsingAnnotation p =
  let ids = parsingIdents p
   in ParsingAnnotation (headOr ids) (parsingOperator p) (headOr (drop 1 ids)) (Cursor.range (nodeSyntax p))

homsItem :: A.HomsItem -> HomSectionItem
homsItem i =
  HomSectionItem
    { hsiName = homsItemName i
    , hsiBindspecs = concatMap (map bindspec . bindspecsOf) (homsItemBindspecs i)
    , hsiHoms = map hom (homsItemHoms i)
    , hsiRange = Cursor.range (nodeSyntax i)
    }

defn :: A.Defn -> Defn
defn d =
  Defn
    { dElements = map element (defnElements d)
    , dCategories = defnCategories d
    , dName = defnName d
    , dWrapper = defnWrapper d
    , dHoms = map hom (defnHoms d)
    , dBody = defnBlocks d
    , dRange = Cursor.range (nodeSyntax d)
    }

-- | The blocks of a definition body as Ott's parser sees them (GRAMMAR.md
-- §4): maximal runs of non-blank lines. A block that holds a rule node is
-- that rule; a block of comment lines only is an empty lineless rule, which
-- Ott keeps in its raw parse and drops later. The tree keeps comment lines
-- as trivia, inside a rule node when Rule 2 gave them to it, so the body is
-- flattened back into lines here.
defnBlocks :: A.Defn -> [SemirawRule]
defnBlocks d = go Nothing False (linesAfterBy (nodeSyntax d))
  where
    -- current: the rule of the open block, if any; open: whether a block is
    -- open (comment lines seen); lines: remaining
    go current open ls = case ls of
      [] -> close current open
      l : more -> case l of
        LBlank -> close current open ++ go Nothing False more
        LComment -> go current True more
        LNode b -> go (Just b) True more
    close current open = case (current, open) of
      (Just b, _) -> [bodyItem b]
      (Nothing, True) -> [LinelessRule [] emptyRange]
      (Nothing, False) -> []
    emptyRange = Cursor.range (nodeSyntax d)

data BodyLine = LBlank | LComment | LNode BodyItem

-- | The lines of a definition body after @by@, classified. A line is blank
-- when it holds only whitespace or a block comment, a comment line when it
-- holds a @%@ comment, and a node line when a rule starts on it. Trivia
-- inside a rule node before its last syntax token never contains a blank
-- line, so only its trailing trivia is examined.
linesAfterBy :: C -> [BodyLine]
linesAfterBy c =
  classify
    ( concatMap flatten (dropWhile (not . isBy) (Cursor.children c))
        ++ map PTok (followingTrivia c)
    )
  where
    isBy t = Cursor.kind t == K.Keyword && A.tokenValue t == T.pack "by"
    flatten t = case A.castBodyItem t of
      Just b ->
        let kids = Cursor.children t
            trailing = reverse (takeWhile (K.isTrivia . Cursor.kind) (reverse kids))
         in PNode b : map (PTok . Cursor.kind) trailing
      Nothing -> [PTok (Cursor.kind t)]
    classify pieces = case pieces of
      [] -> []
      _ ->
        let (line, rest) = break isNewline pieces
            rest' = drop 1 rest
            cls
              | any isNode line = LNode (headNode line)
              | any (== PTok K.LineComment) line = LComment
              | otherwise = LBlank
         in case rest of
              [] | null line -> []
              _ -> cls : classify rest'
    isNewline p = p == PTok K.Newline
    isNode p = case p of
      PNode _ -> True
      _ -> False
    headNode line = case [b | PNode b <- line] of
      (b : _) -> b
      [] -> error "linesAfterBy: no node"

-- | The trivia tokens that follow a node in the document, up to the next
-- syntax token. The body of a definition runs on to the next keyword line,
-- but the tree gives the trivia after a node to its ancestors.
followingTrivia :: C -> [Kind]
followingTrivia c = case Cursor.lastToken c of
  Nothing -> []
  Just lastTok -> go (Cursor.nextToken lastTok)
  where
    go m = case m of
      Just t | K.isTrivia (Cursor.kind t) -> Cursor.kind t : go (Cursor.nextToken t)
      _ -> []

data Piece = PTok Kind | PNode BodyItem

instance Eq Piece where
  PTok a == PTok b = a == b
  _ == _ = False

bodyItem :: BodyItem -> SemirawRule
bodyItem b = case b of
  BodyRule r ->
    LinedRule
      (map lineOf (drulePremises r))
      (maybe T.empty ruleLineAnnotation (druleRuleLine r))
      (case druleRuleLine r of
        Just rl -> RuleAnnot (ruleLineCategories rl) (ruleLineName rl) (map hom (ruleLineHoms rl))
        Nothing -> RuleAnnot [] T.empty [])
      (map lineOf (druleConclusions r))
      (Cursor.range (nodeSyntax r))
  BodyLineless l -> LinelessRule (map lineOf (linelessFormulas l)) (Cursor.range (nodeSyntax l))
  BodyDefnCom c -> DefnComRule (map embedEl (defnComBody c)) (Cursor.range (nodeSyntax c))

-- | A line as Ott's @LINE@ token has it: indentation included.
lineOf :: LineNode -> Text
lineOf l = lineIndent l <> lineText l

fundefn :: A.Fundefn -> FunDefn
fundefn f =
  FunDefn
    { fdElements = map element (fundefnElements f)
    , fdResult = fundefnResult f
    , fdName = fundefnName f
    , fdHoms = map hom (fundefnHoms f)
    , fdClauses = map lineOf (fundefnClauses f)
    , fdRange = Cursor.range (nodeSyntax f)
    }

headOr :: [Text] -> Text
headOr xs = case xs of
  (x : _) -> x
  [] -> T.empty

------------------------------------------------------------------------
-- Merging fragments

-- | Ott's @-merge true@ (@merge_language_fragments@): the grammar rules of
-- the same name are one rule, with the attributes of the first and the
-- productions of all; so are the definition classes, and within them the
-- definitions (whose rules are concatenated) and the functions (whose
-- clauses are). The merged rules take the place of the first grammar
-- item and the merged classes that of the first class.
mergeFragments :: Document -> Document
mergeFragments doc =
  let rules = [r | ItemGrammar rs <- doc, r <- rs]
      classes = [c | it <- doc, c <- classOf it]
      classOf it = case it of
        ItemDefns dc -> [Left dc]
        ItemFuns fc -> [Right fc]
        _ -> []
      ruleKey r = case ruleNames r of
        ((n, _) : _) -> n
        [] -> T.empty
      mergedRules = map (foldr1 (\r r' -> r {ruleProds = ruleProds r ++ ruleProds r'})) (collect ruleKey rules)
      classKey c = case c of
        Left dc -> ("rel", dcName dc)
        Right fc -> ("fun", fcName fc)
      appendClass a b = case (a, b) of
        (Left dc, Left dc') -> Left dc {dcDefns = dcDefns dc ++ dcDefns dc'}
        (Right fc, Right fc') -> Right fc {fcDefns = fcDefns fc ++ fcDefns fc'}
        _ -> error "Haskott.Raw: merge_raw_fun_or_reln_defnclasses 2"
      mergeInside c = case c of
        Left dc -> ItemDefns dc {dcDefns = map (foldr1 (\d d' -> d {dBody = dBody d ++ dBody d'})) (collect dName (dcDefns dc))}
        Right fc -> ItemFuns fc {fcDefns = map (foldr1 (\f f' -> f {fdClauses = fdClauses f ++ fdClauses f'})) (collect fdName (fcDefns fc))}
      mergedClasses = map (mergeInside . foldr1 appendClass) (collect classKey classes)
      go seenG seenC items = case items of
        [] -> []
        ItemGrammar _ : more
          | seenG -> go seenG seenC more
          | otherwise -> ItemGrammar mergedRules : go True seenC more
        it : more
          | not (null (classOf it)) ->
              if seenC then go seenG seenC more else mergedClasses ++ go seenG True more
          | otherwise -> it : go seenG seenC more
   in go False False doc

-- | Ott's @collect@: the items grouped by key, each group in the order
-- of its last member.
collect :: Eq k => (a -> k) -> [a] -> [[a]]
collect key = map snd . foldl step []
  where
    step acc x = case lookup (key x) acc of
      Just ys -> [(k, v) | (k, v) <- acc, k /= key x] ++ [(key x, ys ++ [x])]
      Nothing -> acc ++ [(key x, [x])]
