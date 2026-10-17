{-# LANGUAGE OverloadedStrings #-}

-- | The character-level grammar of symbolic terms, built from the checked
-- specification exactly as Ott's @new_term_parser.ml@ builds it: one
-- nonterminal per rule, metavariable declaration and terminal, builtin
-- nonterminals for whitespace, suffixes, dots, index variables and the
-- lexical classes of concrete variables, generated nonterminals for list
-- forms, pseudo-terminals @:prodname:@ and @:concrete:@, single-character
-- follow restrictions, reject and transparent productions, and the
-- priorities of @parsing@ annotations and list recursion. Each production
-- carries the semantic action that builds its result.
module Haskott.Term.Grammar
  ( NtId
  , Sym (..)
  , Res (..)
  , Tag (..)
  , Production (..)
  , Grammar (..)
  , buildGrammar
  , startSymbol
  ) where

import Control.Monad (forM_, unless, when)
import Control.Monad.Trans.State.Strict (State, get, modify, put, runState)
import qualified Data.IntMap.Strict as IM
import qualified Data.Map.Strict as M
import Data.Maybe (fromMaybe, mapMaybe)
import qualified Data.Set as Set
import Data.Text (Text)
import qualified Data.Text as T
import Haskott.Spec
import Haskott.Syntax.Kind (Kind (..))
import Haskott.Term.Merge
import Haskott.Term.Symterm

type NtId = Int

data Sym = T Char | N NtId
  deriving (Eq, Ord, Show)

-- | Semantic values, as in Ott.
data Res
  = ResSt Symterm
  | ResSte Ste
  | ResStli Stli
  | ResStlil [Stli]
  | ResIgnore
  | ResChar Char
  | ResCharl [Char]
  | ResString Text
  | ResInt Int
  | ResSi SuffixItem
  | ResSil [SuffixItem]
  deriving (Eq, Show)

-- | How a production appears in the lossless tree of a term.
data Tag
  = TagLeaf Kind
  -- ^ one token of the kind, spanning the production minus its leading
  -- whitespace; a 'Space' leaf is the whitespace itself
  | TagPass Kind
  -- ^ no node of its own: its children's elements, with its literal
  -- characters as tokens of the kind
  | TagNode Kind
  -- ^ a node of the kind around its children's elements
  | TagProd Text Text Kind
  -- ^ a production node: the rule's root, the production's name, and the
  -- kind of its literal characters
  deriving (Eq, Show)

data Production = Production
  { prodLeft :: NtId
  , prodRight :: [Sym]
  , prodAction :: [Res] -> Maybe Res
  -- ^ the results of the nonterminals of the right-hand side, in order;
  -- 'Nothing' rejects the parse
  , prodReject :: Bool
  , prodTransparent :: Bool
  , prodIndex :: Int
  , prodTag :: Tag
  }

data Grammar = Grammar
  { gProds :: IM.IntMap Production
  , gByLeft :: IM.IntMap [Int]
  -- ^ production indices per nonterminal
  , gFollow :: IM.IntMap [Char -> Bool]
  -- ^ characters that may not follow a nonterminal
  , gPriority :: M.Map (Int, Int) (Bool, Bool, Bool, Bool)
  -- ^ (parent, child) to (greater, left, right, nonassoc)
  , gStarts :: M.Map (Text, Bool) NtId
  -- ^ rule root and concreteness to its nonterminal
  , gNames :: IM.IntMap Text
  -- ^ nonterminal names, for messages and the grammar printout
  }

-- | The nonterminal to parse a root from, if the grammar has one.
startSymbol :: Grammar -> Text -> Bool -> Maybe NtId
startSymbol g ntr concrete = M.lookup (ntr, concrete) (gStarts g)

------------------------------------------------------------------------
-- The builder

data NtKey
  = OrigNt Text Bool
  | TermNt Text
  | MetavarNt Text Bool
  | BuiltinNt Text
  deriving (Eq, Ord, Show)

data B = B
  { bCount :: !Int
  , bProds :: [Production]
  , bNts :: M.Map NtKey NtId
  , bNames :: IM.IntMap Text
  , bNtCount :: !Int
  , bFollows :: IM.IntMap [Char -> Bool]
  , bPriorities :: [(Text, Int, Int)]
  -- ^ Greater, Left, Right or Nonassoc with two production indices
  , bIndex1 :: M.Map Text Int
  , bIndex2 :: M.Map Text (Int, Int)
  }

type Build = State B

mknt :: NtKey -> Build NtId
mknt k = do
  b <- get
  case M.lookup k (bNts b) of
    Just i -> pure i
    Nothing -> do
      let i = bNtCount b
      put b {bNts = M.insert k i (bNts b), bNtCount = i + 1, bNames = IM.insert i (ntName k) (bNames b)}
      pure i

-- | A fresh generated nonterminal.
gennt :: Text -> Build NtId
gennt base = do
  b <- get
  let i = bNtCount b
  put b {bNtCount = i + 1, bNames = IM.insert i (base <> T.pack (show i)) (bNames b)}
  pure i

ntName :: NtKey -> Text
ntName k = case k of
  OrigNt s c -> (if c then "concrete_" else "") <> s
  TermNt s -> "terminal_" <> s
  MetavarNt s c -> (if c then "concrete_" else "") <> s
  BuiltinNt s -> s

nt :: NtKey -> Build Sym
nt k = N <$> mknt k

addProdWith :: Tag -> Bool -> Bool -> NtId -> [Sym] -> ([Res] -> Maybe Res) -> Build Int
addProdWith tag transp rej left right action = do
  b <- get
  let i = bCount b
      p = Production {prodLeft = left, prodRight = right, prodAction = action, prodReject = rej, prodTransparent = transp, prodIndex = i, prodTag = tag}
  put b {bCount = i + 1, bProds = p : bProds b}
  pure i

plain :: Tag
plain = TagPass TTerminal

addProd :: NtId -> [Sym] -> ([Res] -> Maybe Res) -> Build ()
addProd = addProdT plain

addProdT :: Tag -> NtId -> [Sym] -> ([Res] -> Maybe Res) -> Build ()
addProdT tag l r a = () <$ addProdWith tag False False l r a

addProdIdxT :: Tag -> NtId -> [Sym] -> ([Res] -> Maybe Res) -> Build Int
addProdIdxT tag = addProdWith tag False False

addProdReject :: NtId -> [Sym] -> Build ()
addProdReject l r = () <$ addProdWith plain False True l r (const Nothing)

addProdTransp :: NtId -> [Sym] -> ([Res] -> Maybe Res) -> Build Int
addProdTransp = addProdWith plain True False

addFollow :: NtId -> (Char -> Bool) -> Build ()
addFollow i f = modify (\b -> b {bFollows = IM.insertWith (++) i [f] (bFollows b)})

alphanumRestr :: NtId -> Build ()
alphanumRestr i = addFollow i isAlphanum

numRestr :: NtId -> Build ()
numRestr i = addFollow i (\c -> c >= '0' && c <= '9')

addPriority :: Text -> Int -> Int -> Build ()
addPriority kind i j = modify (\b -> b {bPriorities = (kind, i, j) : bPriorities b})

isAlphanum :: Char -> Bool
isAlphanum c = (c >= 'A' && c <= 'Z') || (c >= 'a' && c <= 'z') || (c >= '0' && c <= '9')

terms :: Text -> [Sym]
terms = map T . T.unpack

ws :: Build Sym
ws = nt (BuiltinNt "whitespace")

-- | The results of the nonterminals of a right-hand side come in order;
-- these helpers destructure them. A pattern that does not match is an
-- internal error in the grammar, not a reject.
res :: Res -> Maybe Res
res = Just

bad :: String -> a
bad s = error ("Haskott.Term.Grammar: unexpected results in " ++ s)

------------------------------------------------------------------------
-- Building

buildGrammar :: Spec -> Grammar
buildGrammar spec =
  let b0 = B 0 [] M.empty IM.empty 0 IM.empty [] M.empty M.empty
      ((), b) = runState (build spec) b0
      prods = IM.fromList [(prodIndex p, p) | p <- bProds b]
      byLeft = IM.fromListWith (flip (++)) [(prodLeft p, [prodIndex p]) | p <- bProds b]
      prio = foldr addPrior M.empty (bPriorities b)
      addPrior (kind, i1, i2) m = case kind of
        "Greater" -> ins (i1, i2) (True, False, False, False) m
        "Left" -> ins (i2, i1) (False, True, False, False) m
        "Right" -> ins (i2, i1) (False, False, True, False) m
        _ -> ins (i2, i1) (False, False, False, True) m
      ins k (g, l, r, n) = M.insertWith (\(g1, l1, r1, n1) (g2, l2, r2, n2) -> (g1 || g2, l1 || l2, r1 || r2, n1 || n2)) k (g, l, r, n)
      starts = M.fromList [((s, c), i) | (OrigNt s c, i) <- M.toList (bNts b)]
   in Grammar
        { gProds = prods
        , gByLeft = IM.map reverse byLeft
        , gFollow = bFollows b
        , gPriority = prio
        , gStarts = starts
        , gNames = bNames b
        }

build :: Spec -> Build ()
build spec = do
  let indexvars = specIndexvars spec
      terminalsSet = Set.fromList (concatMap ruleTerminals (specRules spec))
      isTm s = Set.member s terminalsSet
      mvds = specMetavars spec
      mvdOf r = fromMaybe (error ("no metavar " ++ T.unpack r)) (lookupMvd r)
      lookupMvd r = case [md | md <- mvds, mvdName md == r] of
        (md : _) -> Just md
        [] -> Nothing
      indexMvrs = [n | md <- mvds, mvdIndexvar md, (n, _) <- mvdNames md]
      nonindexMvrs = [n | md <- mvds, not (mvdIndexvar md), (n, _) <- mvdNames md]
      allNtrs = [n | r <- specRules spec, (n, _) <- ruleNames r]
      ntrSynonyms ntr = concat [map fst (ruleNames r) | r <- specRules spec, ruleName r == ntr]
      properSubs ntr = fromMaybe [] (lookup ntr (srdProperSubntrs (specSubruleData spec)))
      promote ntr = case [srTop s | s <- specSubrules spec, srLower s == ntr] of
        (t : _) -> t
        [] -> ntr
      concreteParsers =
        [("alphanum0", BuiltinNt "alphanum0"), ("alphanum", BuiltinNt "alphanum"), ("Alphanum", BuiltinNt "Alphanum"), ("numeral", BuiltinNt "digit_plus2")]
      lexOf md = case lookup "lex" (mvdHoms md) of
        Just [HomString s] -> Just s
        _ -> Nothing

  -- builtins
  whitespace <- mknt (BuiltinNt "whitespace")
  addProdT (TagLeaf Space) whitespace [] (const (res ResIgnore))
  forM_ (" \n\t\r\f" :: String) $ \c -> addProdT (TagLeaf Space) whitespace [N whitespace, T c] (const (res ResIgnore))

  digit <- mknt (BuiltinNt "digit")
  forM_ ['0' .. '9'] $ \c -> addProd digit [T c] (const (res (ResChar c)))
  digitPlus <- mknt (BuiltinNt "digit_plus")
  addProd digitPlus [N digit] (\rs -> case rs of [ResChar c] -> res (ResCharl [c]); _ -> bad "digit_plus")
  addProd digitPlus [N digit, N digitPlus] resCharl
  numRestr digitPlus
  digitPlus2 <- mknt (BuiltinNt "digit_plus2")
  addProd digitPlus2 [N digitPlus] (\rs -> case rs of [ResCharl s] -> res (ResString (T.pack s)); _ -> bad "digit_plus2")
  alphanumRestr digitPlus2

  dots <- mknt (BuiltinNt "dots")
  addProdT (TagLeaf Dots) dots (terms "..") (const (res (ResInt 0)))
  addProdT (TagLeaf Dots) dots (terms "...") (const (res (ResInt 1)))
  addProdT (TagLeaf Dots) dots (terms "....") (const (res (ResInt 2)))

  suffix <- mknt (BuiltinNt "suffix")
  suffixItem <- mknt (BuiltinNt "suffix_item")
  addProd suffix [] (const (res (ResSil [])))
  addProd suffix [N suffixItem, N suffix] (\rs -> case rs of [ResSi s, ResSil sl] -> res (ResSil (s : sl)); _ -> bad "suffix")
  alphanumRestr suffix
  indexvarFancy <- mknt (BuiltinNt "indexvar_fancy_suffix")
  addProd suffixItem [N digitPlus] (\rs -> case rs of [ResCharl l] -> res (ResSi (SiNum (T.pack l))); _ -> bad "suffix_item")
  addProd suffixItem [T '_'] (const (res (ResSi (SiPunct "_"))))
  addProd suffixItem [T '\''] (const (res (ResSi (SiPunct "'"))))
  addProd suffixItem [N indexvarFancy] (\rs -> case rs of [r] -> res r; _ -> bad "suffix_item fancy")

  capAz <- mknt (BuiltinNt "cap_az")
  forM_ ['A' .. 'Z'] $ \c -> addProd capAz [T c] (const (res (ResChar c)))
  az <- mknt (BuiltinNt "az")
  forM_ ['a' .. 'z'] $ \c -> addProd az [T c] (const (res (ResChar c)))
  alphaFollow <- mknt (BuiltinNt "alpha_follow")
  addProd alphaFollow [] (const (res (ResCharl [])))
  addProd alphaFollow [N az, N alphaFollow] resCharl
  addProd alphaFollow [N capAz, N alphaFollow] resCharl
  addProd alphaFollow [N digit, N alphaFollow] resCharl
  addProd alphaFollow [T '_', N alphaFollow] (\rs -> case rs of [ResCharl c] -> res (ResCharl ('_' : c)); _ -> bad "alpha_follow")
  addProd alphaFollow [T '\'', N alphaFollow] (\rs -> case rs of [ResCharl c] -> res (ResCharl ('\'' : c)); _ -> bad "alpha_follow")
  alphanum0 <- mknt (BuiltinNt "alphanum0")
  addProd alphanum0 [N az, N alphaFollow] resConsString
  alphanumRestr alphanum0
  alphanum <- mknt (BuiltinNt "alphanum")
  addProd alphanum [N az, N alphaFollow] resConsString
  addProd alphanum [N capAz, N alphaFollow] resConsString
  alphanumRestr alphanum
  capAlphanum <- mknt (BuiltinNt "Alphanum")
  addProd capAlphanum [N capAz, N alphaFollow] resConsString
  alphanumRestr capAlphanum
  number <- mknt (BuiltinNt "number")
  addProdT (TagLeaf TNumber) number [T '0'] (const (res (ResString "0")))
  addProdT (TagLeaf TNumber) number [T '1'] (const (res (ResString "1")))
  alphanumRestr number

  indexvar <- mknt (BuiltinNt "indexvar")
  forM_ indexvars $ \iv -> addProdT (TagLeaf TIndex) indexvar (terms iv) (const (res (ResString iv)))
  addProdT (TagLeaf TIndex) indexvarFancy [N indexvar] (\rs -> case rs of [ResString s] -> res (ResSi (SiVar s 0)); _ -> bad "indexvar_fancy")
  addProdT (TagLeaf TIndex) indexvarFancy (N indexvar : terms "-1") (\rs -> case rs of [ResString s] -> res (ResSi (SiVar s (-1))); _ -> bad "indexvar_fancy")

  -- nt_or_mv: anything that lexes as a nonterminal or metavariable
  ntOrMv <- mknt (BuiltinNt "nt_or_mv")
  let addMvrNonidx target name mvr = do
        addProdT (TagLeaf TMetavar) target (N whitespace : terms mvr) (const (res (ResSte (SteMetavar name (mvr, [])))))
        alphanumRestr target
      addMvrIdx target name mvr =
        addProdT (TagLeaf TMetavar) target (N whitespace : terms mvr ++ [N suffix]) (\rs -> case rs of [_, ResSil x] -> res (ResSte (SteMetavar name (mvr, x))); _ -> bad "mvr idx")
  forM_ indexMvrs (addMvrNonidx ntOrMv "")
  forM_ nonindexMvrs (addMvrIdx ntOrMv "")
  forM_ allNtrs $ \n ->
    addProd ntOrMv (N whitespace : terms n ++ [N suffix]) (\rs -> case rs of [_, ResSil x] -> res (ResSt (StNonterm "" (n, x))); _ -> bad "nt_or_mv ntr")

  -- metavariables
  forM_ mvds $ \md -> do
    mnt <- mknt (MetavarNt (mvdName md) False)
    forM_ (mvdNames md) $ \(mvr, _) ->
      if mvdIndexvar md then addMvrNonidx mnt (mvdName md) mvr else addMvrIdx mnt (mvdName md) mvr
    case lexOf md >>= \r -> lookup r concreteParsers of
      Nothing -> pure ()
      Just lexNt -> do
        lexSym <- nt lexNt
        addProdT (TagLeaf TMetavar) mnt (N whitespace : T ':' : terms (mvdName md) ++ [T ':', lexSym])
          (\rs -> case rs of (_ : ResString s : _) -> res (ResSte (SteMetavar (mvdName md) (s, []))); _ -> bad "metavar :name:")
        ntAux <- gennt (mvdName md <> "_aux")
        ntC <- mknt (MetavarNt (mvdName md) True)
        addProdT (TagLeaf TVar) ntC [N whitespace, lexSym]
          (\rs -> case rs of [_, ResString s] -> if isTm s then Nothing else res (ResSte (SteVar (mvdName md) s)); _ -> bad "concrete var")
        addProdT (TagLeaf TVar) ntAux [N whitespace, lexSym]
          (\rs -> case rs of [_, ResString s] -> res (ResSte (SteVar (mvdName md) s)); _ -> bad "var aux")
        addProdReject ntAux [N ntOrMv]
        addProd mnt [N ntAux]
          (\rs -> case rs of [x@(ResSte (SteVar _ s))] -> if isTm s then Nothing else res x; _ -> bad "var")

  -- rules
  forM_ (specRules spec) $ \r -> do
    let ntr = ruleName r
    rnt <- mknt (OrigNt ntr False)
    unless (ruleMeta r) $ do
      let concreteProds = [p | p <- ruleProds r, not (prodMeta p) || prodSugar p]
      ntC <- mknt (OrigNt ntr True)
      forM_ concreteProds (processProd mvdOf True ntC ntr)
      addProdT (TagPass TProdName) rnt (N whitespace : terms ":concrete:" ++ [N ntC]) (\rs -> case rs of [_, x] -> res x; _ -> bad "concrete")
    forM_ (ruleProds r) (processProd mvdOf False rnt ntr)
    forM_ (ntrSynonyms ntr) $ \n ->
      addProdT (TagLeaf TNonterm) rnt (N whitespace : terms n ++ [N suffix]) (\rs -> case rs of [_, ResSil l] -> res (ResSt (StNonterm ntr (n, l))); _ -> bad "nonterm")
    forM_ (properSubs ntr) $ \ntl ->
      forM_ (ntrSynonyms ntl) $ \n ->
        addProdT (TagLeaf TNonterm) rnt (N whitespace : terms n ++ [N suffix]) (\rs -> case rs of [_, ResSil l] -> res (ResSt (StNontermSub ntl (promote ntr) (n, l))); _ -> bad "nontermsub")

  -- terminals
  forM_ (Set.toList terminalsSet) $ \t -> do
    tnt <- mknt (TermNt t)
    addProdT (TagLeaf TTerminal) tnt (N whitespace : terms t) (\rs -> case rs of [x] -> res x; _ -> bad "terminal")
    when (T.null t || isAlphanum (T.last t)) (alphanumRestr tnt)

  -- priorities of parsing annotations
  b <- get
  forM_ (specParsing spec) $ \pa -> do
    let (i1, i1') = fromMaybe (bad "parsing annotation") (M.lookup (paLeft pa) (bIndex2 b))
        (i2, i2') = fromMaybe (bad "parsing annotation") (M.lookup (paRight pa) (bIndex2 b))
        entries = case paOperator pa of
          "<=" -> [("Greater", i2, i1), ("Greater", i2', i1)]
          "left" -> [("Left", i1, i2), ("Left", i1', i2)]
          "right" -> [("Right", i1, i2), ("Right", i1', i2)]
          _ -> [("Nonassoc", i1, i2), ("Nonassoc", i1', i2)]
        concreteEntries = case (M.lookup (paLeft pa) (bIndex1 b), M.lookup (paRight pa) (bIndex1 b)) of
          (Just c1, Just c2) -> case paOperator pa of
            "<=" -> [("Greater", c2, c1)]
            "left" -> [("Left", c1, c2)]
            "right" -> [("Right", c1, c2)]
            _ -> [("Nonassoc", c1, c2)]
          _ -> []
    forM_ (concreteEntries ++ entries) $ \(k, i, j) -> addPriority k i j
  where
    resCharl rs = case rs of
      [ResChar c, ResCharl l] -> res (ResCharl (c : l))
      _ -> bad "charl"
    resConsString rs = case rs of
      [ResChar c, ResCharl l] -> res (ResString (T.pack (c : l)))
      _ -> bad "cons_string"

ruleTerminals :: Rule -> [Text]
ruleTerminals r = concatMap elementTerminals [e | p <- ruleProds r, e <- prodElements p]
  where
    elementTerminals e = case e of
      Terminal t -> [t]
      ListForm lb -> maybe [] pure (lbSeparator lb) ++ concatMap elementTerminals (lbElements lb)
      _ -> []

-- | A production of a rule: its right-hand side, and the variant with the
-- @:prodname:@ pseudo-terminal (or the disambiguate hom's delimiters).
processProd :: (Text -> MetavarDefn) -> Bool -> NtId -> Text -> Prod -> Build ()
processProd mvdOf concrete left ntr p = do
  let buildRes rl = res (ResSt (StNode ntr (prodName p) (processProdRes rl)))
  rhs <- mapM (processElement mvdOf concrete left) (prodElements p)
  index <- addProdIdxT (TagProd ntr (prodName p) TTerminal) left rhs buildRes
  if concrete
    then modify (\b -> b {bIndex1 = M.insert (prodName p) index (bIndex1 b)})
    else case prodDisambiguate p of
      Nothing -> do
        w <- ws
        index2 <- addProdIdxT (TagProd ntr (prodName p) TProdName) left (w : terms (":" <> prodName p <> ":") ++ rhs) (\rs -> case rs of (_ : rl) -> buildRes rl; _ -> bad "pseudo-terminal")
        modify (\b -> b {bIndex2 = M.insert (prodName p) (index, index2) (bIndex2 b)})
      Just (s1, s2) -> do
        w <- ws
        index2 <- addProdIdxT (TagProd ntr (prodName p) TTerminal) left (w : terms s1 ++ rhs ++ terms s2) (\rs -> case rs of (_ : rl) -> buildRes rl; _ -> bad "disambiguate")
        modify (\b -> b {bIndex2 = M.insert (prodName p) (index, index2) (bIndex2 b)})

processProdRes :: [Res] -> [Ste]
processProdRes = mapMaybe toSte
  where
    toSte r = case r of
      ResIgnore -> Nothing
      ResSte ste -> Just ste
      ResSt st -> Just (SteSt st)
      _ -> bad "production results"

processElement :: (Text -> MetavarDefn) -> Bool -> NtId -> Element -> Build Sym
processElement mvdOf concrete left e = case e of
  Terminal t -> nt (TermNt t)
  Nonterm ntrp _ _ -> nt (OrigNt ntrp concrete)
  Metavar mvrp _ _ -> nt (MetavarNt (mvdName (mvdOf mvrp)) concrete)
  ListForm lb -> do
    let elc = enforceLength lb
    listNt <- gennt "list"
    addProdT (TagNode TList) listNt [] (const (elc []))
    helpNt <- processListForm mvdOf concrete left lb
    addProdT (TagNode TList) listNt [N helpNt] (\rs -> case rs of [ResStlil x] -> elc x; _ -> bad "list")
    pure (N listNt)

enforceLength :: ListBody -> [Stli] -> Maybe Res
enforceLength lb stlis =
  let constraint = case lbBound lb of
        Just (BoundDotform _ _ n) -> Just n
        Just (BoundCompLU _ _ _ n) -> Just n
        _ -> Nothing
      minLength = sum (map stliMin stlis)
      stliMin s = case s of
        StliSingle _ -> 1
        StliListform _ _ -> 2
   in case constraint of
        Just lc | minLength < lc -> Nothing
        _ -> res (ResSte (SteList stlis))

-- | The list nonterminals of a list form, returning the one for a
-- non-empty list.
processListForm :: (Text -> MetavarDefn) -> Bool -> NtId -> ListBody -> Build NtId
processListForm mvdOf concrete left lb = do
  helpNt <- gennt "list_help"
  entryNt <- gennt "list_entry"
  w <- ws
  entryRhs <- mapM (processElement mvdOf concrete left) (lbElements lb)
  addProdT (TagNode TEntry) entryNt entryRhs (\rl -> res (ResStli (StliSingle (processProdRes rl))))
  addProd helpNt [N entryNt] (\rs -> case rs of [ResStli x] -> res (ResStlil [x]); _ -> bad "list_help")
  idx <- case lbSeparator lb of
    Nothing -> do
      addProdReject helpNt []
      addProdTransp helpNt [N entryNt, N helpNt] resStlil
    Just t -> addProdTransp helpNt ([N entryNt, w] ++ terms t ++ [N helpNt]) (\rs -> case rs of [x, _, y] -> resStlil [x, y]; _ -> bad "list_help sep")
  addPriority "Right" idx idx
  unless concrete $ do
    formNt <- gennt "list_form"
    dotsSym <- nt (BuiltinNt "dots")
    indexvarSym <- nt (BuiltinNt "indexvar")
    numberSym <- nt (BuiltinNt "number")
    fancySym <- nt (BuiltinNt "indexvar_fancy_suffix")
    let token t = w : terms t
        prefix = token "</" ++ [N entryNt] ++ token "//" ++ [w, indexvarSym]
        dotRes es1 n' es2 = case mergeSteListShifts es1 es2 of
          Just (Just (si1, si2), es'') -> res (ResStli (StliListform (BoundDotform si1 si2 n') es''))
          _ -> Nothing
    case lbSeparator lb of
      Nothing ->
        addProdT (TagNode TListForm) formNt [N entryNt, w, dotsSym, N entryNt]
          (\rs -> case rs of
            [ResStli (StliSingle es1), _, ResInt n', ResStli (StliSingle es2)] -> dotRes es1 n' es2
            _ -> bad "dot form")
      Just t ->
        addProdT (TagNode TListForm) formNt ([N entryNt, w] ++ terms t ++ [w, dotsSym, w] ++ terms t ++ [N entryNt])
          (\rs -> case rs of
            [ResStli (StliSingle es1), _, _, ResInt n', _, ResStli (StliSingle es2)] -> dotRes es1 n' es2
            _ -> bad "dot form sep")
    addProdT (TagNode TListForm) formNt (prefix ++ token "/>")
      (\rs -> case rs of
        [_, ResStli (StliSingle es), _, _, ResString ivr, _] ->
          res (ResStli (StliListform (BoundComp ivr) (map (abstractIndexvarSte ivr 0) es)))
        _ -> bad "comp")
    addProdT (TagNode TListForm) formNt (prefix ++ token "IN" ++ [w, indexvarSym] ++ token "/>")
      (\rs -> case rs of
        [_, ResStli (StliSingle es), _, _, ResString ivr, _, _, ResString ivr', _] ->
          res (ResStli (StliListform (BoundCompU ivr (SiVar ivr' 0)) (map (abstractIndexvarSte ivr 0) es)))
        _ -> bad "comp u")
    addProdT (TagNode TListForm) formNt (prefix ++ token "IN" ++ [w, numberSym, w, dotsSym, w, fancySym] ++ token "/>")
      (\rs -> case rs of
        [_, ResStli (StliSingle es), _, _, ResString ivr, _, _, ResString lower, _, ResInt n, _, ResSi si', _] ->
          res (ResStli (StliListform (BoundCompLU ivr (SiNum lower) si' n) (map (abstractIndexvarSte ivr 0) es)))
        _ -> bad "comp lu")
    addProd helpNt [N formNt] (\rs -> case rs of [ResStli x] -> res (ResStlil [x]); _ -> bad "list_help form")
    case lbSeparator lb of
      Nothing -> () <$ addProdTransp helpNt [N formNt, N helpNt] resStlil
      Just t -> () <$ addProdTransp helpNt ([N formNt, w] ++ terms t ++ [N helpNt]) (\rs -> case rs of [x, _, y] -> resStlil [x, y]; _ -> bad "list_help form sep")
  pure helpNt
  where
    resStlil rs = case rs of
      [ResStli a, ResStlil b] -> res (ResStlil (a : b))
      _ -> bad "stlil"
