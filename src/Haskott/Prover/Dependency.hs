{-# LANGUAGE OverloadedStrings #-}

-- | Ott's @dependency.ml@: the dependencies between the rules and
-- metavariables of a specification, which group mutually recursive types
-- and order them, and the sorting, collapsing and printing of mutually
-- recursive functions. The order of the groups is ocamlgraph's, so the
-- graphs are those of "Haskott.Graph" and every computation threads the
-- vertex counter.
module Haskott.Prover.Dependency
  ( computeDependencies
  , primaryNtrsUsedInRule
  , primaryMvrsUsedInRule
  , Footer (..)
  , IntFunc (..)
  , IntFuncs (..)
  , Collapsed
  , collapse
  , sortFuncs
  , printFuncs
  , compute
  ) where

import Control.Monad.Trans.State.Strict (get, modify)
import Data.List (find, partition)
import qualified Data.IntSet as IS
import qualified Data.Map.Strict as M
import Data.Maybe (fromMaybe, mapMaybe)
import qualified Data.Set as Set
import Data.Text (Text)
import qualified Data.Text as T
import qualified Haskott.Graph as G
import Haskott.Prover.Types
import Haskott.Spec

------------------------------------------------------------------------
-- The roots a rule uses

splitBlanks :: Text -> [Text]
splitBlanks = filter (not . T.null) . T.split (`elem` (" \t" :: String))

-- | Ott's @primary_ntrs_used_in_rule xd false scan_homs promote@: the
-- primary roots of the non-meta productions, promoted to their top rule if
-- asked, and the roots a hom of the given name mentions.
primaryNtrsUsedInRule :: Spec -> Maybe Text -> Bool -> Rule -> Set.Set Text
primaryNtrsUsedInRule spec scanHoms promote r =
  let prods = filter (not . prodMeta) (ruleProds r)
      inRule = Set.unions (map (elementsNtrs . prodElements) prods)
      elementsNtrs = Set.unions . map elementNtrs
      elementNtrs e = case e of
        Nonterm p _ _ -> Set.singleton (prom p)
        ListForm lb -> elementsNtrs (lbElements lb)
        _ -> Set.empty
      prom n = if promote then promoteIn spec n else n
      defined = Set.fromList [n | r' <- specRules spec, (n, _) <- ruleNames r']
   in case scanHoms of
        Nothing -> inRule
        Just m -> Set.union inRule (homStrings m (ruleHoms r) (\w -> if Set.member w defined then Just (prom w) else Nothing))

primaryMvrsUsedInRule :: Spec -> Maybe Text -> Rule -> Set.Set Text
primaryMvrsUsedInRule spec scanHoms r =
  let prods = filter (not . prodMeta) (ruleProds r)
      elementsMvrs = Set.unions . map elementMvrs
      elementMvrs e = case e of
        Metavar p _ _ -> Set.singleton p
        ListForm lb -> elementsMvrs (lbElements lb)
        _ -> Set.empty
      inRule = Set.unions (map (elementsMvrs . prodElements) prods)
      defined = Set.fromList [n | md <- specMetavars spec, (n, _) <- mvdNames md]
   in case scanHoms of
        Nothing -> inRule
        Just m -> Set.union inRule (homStrings m (ruleHoms r) (\w -> if Set.member w defined then Just w else Nothing))

homStrings :: Text -> [Hom] -> (Text -> Maybe Text) -> Set.Set Text
homStrings m homs keep = case lookup m homs of
  Nothing -> Set.empty
  Just hs -> Set.fromList (concat [mapMaybe keep (splitBlanks s) | HomString s <- hs])

promoteIn :: Spec -> Text -> Text
promoteIn spec n = maybe n srTop (find ((== n) . srLower) (specSubrules spec))

------------------------------------------------------------------------
-- Dependencies of the syntax

-- | Ott's @compute_dependencies@ for a target (or @ascii@), with the
-- vertex counter: the vertices of the graph, of its components, and of
-- the copy the transitive closure makes.
computeDependencies :: Spec -> Text -> Int -> (Deps, Int)
computeDependencies spec m counter0 =
  let classes = [Left (map fst (ruleNames r)) | r <- specRules spec] ++ [Right (map fst (mvdNames md)) | md <- specMetavars spec]
      -- the vertices, newest first as in Ott's association list
      (info, counter1) = newVertices counter0 classes
      g0 = foldl' (flip G.addVertex) G.create (map fst (reverse info))
      names = either id id
      vertexOf n = maybe (error ("Haskott.Prover.Dependency: no vertex for " ++ T.unpack n)) fst (find (\(_, cl) -> n `elem` names cl) info)
      ruleEdges r =
        [ (vertexOf (ruleName r), vertexOf n)
        | n <- Set.toList (primaryNtrsUsedInRule spec (Just m) True r) ++ Set.toList (primaryMvrsUsedInRule spec (Just m) r)
        ]
      g = foldl' (\gr (a, b) -> G.addEdge a b gr) g0 (concatMap ruleEdges (specRules spec))
      (sg, sccInfo, counter2) = componentGraph g counter1
      back cl = case cl of
        Left (n : _) -> Ntr n
        Right (n : _) -> Mvr n
        _ -> error "Haskott.Prover.Dependency: a class without names"
      classOf v = maybe (error "Haskott.Prover.Dependency: no class") snd (find ((== v) . fst) info)
      dump sv rl = foldr (\v r -> back (classOf v) : r) [] (fromMaybe [] (lookup sv sccInfo)) : rl
      ts = G.topologicalFold dump sg []
      closure = G.transitiveSuccs g
      vs = G.vertices g
      -- G.succ order (decreasing tags) on the closure and on g; the
      -- reversals are Ott's consing onto a ref
      depGr = reverse [(back (classOf v), [back (classOf w) | w <- reverse vs', IS.member (G.vTag w) (closure M.! v)]) | v <- vs, let vs' = sortTags vs]
      depNon = reverse [(back (classOf v), [back (classOf w) | w <- G.succsDecreasing g v]) | v <- vs]
      sortTags = map snd . M.toList . M.fromList . map (\v -> (G.vTag v, v))
   in (Deps ts depGr depNon, counter2 + G.copyCount g)

-- | New vertices labelled 0, 1, ... for the items, newest first.
newVertices :: Int -> [a] -> ([(G.Vertex, a)], Int)
newVertices c0 xs =
  let (acc, c, _) = foldl' (\(acc', c', lbl) x -> let (v, c'') = G.newVertex c' lbl in ((v, x) : acc', c'', lbl + 1)) ([], c0, 0 :: Int) xs
   in (acc, c)

-- | The graph of the strongly connected components of a graph, without
-- self-loops, and its vertices with their components, newest first.
componentGraph :: G.Graph -> Int -> (G.Graph, [(G.Vertex, [G.Vertex])], Int)
componentGraph g c0 =
  let (sccInfo, c1) = newVertices c0 (G.sccList g)
      sg0 = foldl' (flip G.addVertex) G.create (map fst (reverse sccInfo))
      sccOf v = maybe (error "Haskott.Prover.Dependency: no component") fst (find (\(_, vs) -> v `elem` vs) sccInfo)
      sg1 = foldl' (\gr (s, d) -> G.addEdge (sccOf s) (sccOf d) gr) sg0 (G.edges g)
      sg = foldl' (\gr v -> G.removeEdge v v gr) sg1 (G.vertices sg1)
   in (sg, sccInfo, c1)

------------------------------------------------------------------------
-- Functions

data Footer
  = FooterEmpty
  | FooterIsaProjLemma Text Text Text
  | FooterProof Text
  deriving (Eq, Show)

-- | Ott's @int_func@: a function before collapsing.
data IntFunc = IntFunc
  { rFunId :: Text
  , rFunDep :: [Text]
  , rFunType :: Text
  , rFunHeader :: (Text, Text, Text)
  , rFunClauses :: [(Text, Text, Text)]
  }

data IntFuncs = IntFuncs
  { iFuncs :: [IntFunc]
  , iFuncsProof :: Maybe Text
  }

-- | Ott's @int_funcs_collapsed@: each function's name, dependencies,
-- header, body and footer.
type Collapsed = [(Text, [Text], ((Text, Text, Text), Text, Footer))]

-- | Ott's @Dependency.collapse@.
collapse :: Env -> IntFuncs -> Collapsed
collapse env funcs0 =
  let funcs = funcs0 {iFuncs = removeDupFuncs (iFuncs funcs0)}
      opts = envOpts env
      each sep clause footer = [(i, d, (h, T.intercalate sep (map (clause i) cs), footer)) | IntFunc i d _ h cs <- iFuncs funcs]
      proof = buildFooter (iFuncsProof funcs)
   in case envTarget env of
        Isa
          | optIsaPrimrec opts -> isaPrimrecCollapse funcs
          | otherwise -> each "| " (\i (_, l, r) -> "\"" <> i <> " " <> l <> " = (" <> r <> ")\"\n") proof
        Hol -> each "/\\" (\i (_, l, r) -> "  ( " <> i <> " " <> l <> " = " <> r <> ")\n") proof
        Lem -> each "" (\_ (_, l, r) -> "   | " <> l <> " -> " <> r <> "\n") FooterEmpty
        Coq -> each "" (\_ (_, l, r) -> "  | " <> l <> " => " <> r <> "\n") FooterEmpty
        Caml -> each "" (\_ (_, l, r) -> "  | " <> l <> " -> " <> r <> "\n") FooterEmpty
        Twf -> each "" (\i (pfx, l, r) -> i <> "/" <> pfx <> " : " <> i <> " " <> l <> " " <> r <> ".\n") FooterEmpty

buildFooter :: Maybe Text -> Footer
buildFooter = maybe FooterEmpty FooterProof

-- | Ott's @remove_duplicates@ on functions: the last of each name stays.
removeDupFuncs :: [IntFunc] -> [IntFunc]
removeDupFuncs fs = case fs of
  [] -> []
  x : xs -> if any ((== rFunId x) . rFunId) xs then removeDupFuncs xs else x : removeDupFuncs xs

-- | Ott's @isa_primrec_collapse@: functions over the same type are
-- collapsed into one returning a tuple, with projections.
isaPrimrecCollapse :: IntFuncs -> Collapsed
isaPrimrecCollapse funcs =
  let groups = group (iFuncs funcs) []
      group fs carry = case fs of
        [] -> reverse carry
        x : xs ->
          let (a, b) = partition (\y -> rFunType x == rFunType y) xs
           in group b ((x : a) : carry)
      collapseClause i (_, l, r) = "\"" <> i <> " " <> l <> " = (" <> r <> ")\"\n"
      collapseFunc f = (rFunId f, rFunDep f, (rFunHeader f, T.intercalate "| " (map (collapseClause (rFunId f)) (rFunClauses f)), FooterEmpty))
      collapseGroup g = case g of
        [f] -> (collapseFunc f, [])
        _ -> collapseBigGroup g
      (collapsed, substs0) = unzip (map collapseGroup groups)
      substs = concat substs0
      updateDeps ds = removeDuplicates [maybe d (\(p, _, _) -> p) (lookup d substs) | d <- ds]
      substitute s = foldl' substituteOne s substs
      substituteOne s (orig, (_, sub, _)) = replaceApplications orig sub s
   in [(i, updateDeps d, (h, substitute body, footer)) | (i, d, (h, body, footer)) <- collapsed]
  where
    collapseBigGroup g =
      let ids = map rFunId g
          ident = T.intercalate "_" ids
          projection x = (x, (ident, "(%(" <> T.intercalate "," ids <> ")." <> x <> ") (" <> ident, "(%(" <> T.intercalate "," ids <> ")." <> x <> ") o " <> ident))
          projections = map projection ids
          deps = concatMap rFunDep g
          headerOf f = let (h, _, _) = rFunHeader f in h
          inpType f = fromMaybe (error "Haskott.Prover.Dependency: cannot extract the inp type from the header") (extractInpType (headerOf f))
          retType f = fromMaybe (error "Haskott.Prover.Dependency: cannot extract the out type from the header") (extractRetType (headerOf f))
          (first, it) = case g of
            f : _ -> (f, inpType f)
            [] -> error "Haskott.Prover.Dependency: an empty group"
          outputType = "(" <> T.intercalate ") * (" (map retType g) <> ")"
          header = ident <> " :: \"" <> it <> " => " <> outputType <> "\"\n"
          lhsOf f = [l | (_, l, _) <- rFunClauses f]
          rhsOf f = [r | (_, _, r) <- rFunClauses f]
          lhs = lhsOf first
          rhsLines = transpose' (map rhsOf g)
          rhs = map (T.intercalate " , ") rhsLines
          clauses = zipWith (\l r -> (T.empty, l, r)) lhs rhs
          collapsedBody = T.intercalate "| " (map (\(_, l, r) -> "\"" <> ident <> " " <> l <> " = (" <> r <> ")\"\n") clauses)
          makeDefinition f =
            "definition " <> rFunId f <> " :: \"" <> it <> " => " <> retType f <> "\" where\n"
              <> "\"" <> rFunId f <> " == " <> maybe "" (\(_, _, x) -> x) (lookup (rFunId f) projections) <> "\"\n"
          projText = T.intercalate "\n" (map makeDefinition g) <> "\n"
          lemmaClauses f = T.intercalate "\n" ["\"" <> rFunId f <> " " <> l <> " = " <> r <> "\"" | (_, l, r) <- rFunClauses f]
          lemma = T.intercalate "\n" (map lemmaClauses g) <> "\n"
          defs = T.unwords [rFunId f <> "_def" | f <- g]
       in ((ident, deps, ((header, "", ""), collapsedBody, FooterIsaProjLemma projText lemma defs)), projections)
    transpose' m = case m of
      [] -> []
      (r : _) -> foldl' (\acc xs -> zipWith (:) xs acc) (map (const []) r) (reverse m)

-- | The input type of an Isabelle header @f :: "a => b"@, by Ott's
-- regular expression @.*"\\(.*\\) =>.*@ (greedy, on the first line).
extractInpType :: Text -> Maybe Text
extractInpType h =
  let line = T.takeWhile (/= '\n') h
      arrows = occurrences " =>" line
      quotes = [i | (i, ch) <- zip [0 ..] (T.unpack line), ch == '"']
   in case arrows of
        [] -> Nothing
        _ ->
          let p = last arrows
           in case filter (< p) quotes of
                [] -> Nothing
                qs -> let q = last qs in Just (T.take (p - q - 1) (T.drop (q + 1) line))

-- | The result type, by @.*=> \\(.*\\)"@.
extractRetType :: Text -> Maybe Text
extractRetType h =
  let line = T.takeWhile (/= '\n') h
      quotes = [i | (i, ch) <- zip [0 ..] (T.unpack line), ch == '"']
   in case quotes of
        [] -> Nothing
        _ ->
          let q = last quotes
           in case filter (\p -> p + 3 <= q) (occurrences "=> " line) of
                [] -> Nothing
                ps -> let p = last ps in Just (T.take (q - p - 3) (T.drop (p + 3) line))

-- | The character offsets at which a pattern occurs.
occurrences :: Text -> Text -> [Int]
occurrences pat t = [i | i <- [0 .. T.length t - T.length pat], pat `T.isPrefixOf` T.drop i t]

-- | Ott's replacement of @(orig args)@ by @(sub args))@, everywhere.
replaceApplications :: Text -> Text -> Text -> Text
replaceApplications orig sub = go
  where
    pat = "(" <> orig <> " "
    go t = case T.breakOn pat t of
      (before, rest)
        | T.null rest -> t
        | otherwise ->
            let (args, rest') = T.break (== ')') (T.drop (T.length pat) rest)
             in if T.null rest'
                  then t
                  else before <> "(" <> sub <> " " <> args <> "))" <> go (T.drop 1 rest')

removeDuplicates :: Eq a => [a] -> [a]
removeDuplicates xs = case xs of
  [] -> []
  x : more -> if x `elem` more then removeDuplicates more else x : removeDuplicates more

-- | Ott's @Dependency.sort@: the functions grouped into mutually
-- recursive blocks in dependency order, and those that call themselves.
sortFuncs :: Collapsed -> P ([[(Text, ((Text, Text, Text), Text, Footer))]], [Text])
sortFuncs l = do
  c0 <- psVertex <$> get
  let names = [x | (x, _, _) <- l]
      (info, c1) = newVertices c0 names
      g0 = foldl' (flip G.addVertex) G.create (map fst (reverse info))
      vertexOf n = fst <$> find ((== n) . snd) info
      g = foldl' addE g0 [(sn, tn) | (sn, tnl, _) <- l, tn <- tnl]
      addE gr (sn, tn) = case (vertexOf sn, vertexOf tn) of
        (Just a, Just b) | not (G.memEdge a b gr) -> G.addEdge a b gr
        _ -> gr
      (sg, sccInfo, c2) = componentGraph g c1
      nameOf v = maybe (error "Haskott.Prover.Dependency: no name") snd (find ((== v) . fst) info)
      valueOf a = case [s | (x, _, s) <- l, x == a] of
        (s : _) -> s
        [] -> error "Haskott.Prover.Dependency: no function"
      dump sn rl = foldr (\v r -> let a = nameOf v in (a, valueOf a) : r) [] (fromMaybe [] (lookup sn sccInfo)) : rl
      topSort = G.topologicalFold dump sg []
      singletons = concat (filter ((== 1) . length) topSort)
      recSingletons = [x | (x, _) <- singletons, Just v <- [vertexOf x], G.memEdge v v g]
  modify (\s -> s {psVertex = c2})
  pure (topSort, recSingletons)

-- | Ott's @Dependency.print@.
printFuncs :: Env -> ([[(Text, ((Text, Text, Text), Text, Footer))]], [Text]) -> Text
printFuncs env (sorting, refl) = case envTarget env of
  Isa -> T.concat (map isaBlock sorting)
  Hol -> T.intercalate "\n" (map holBlock sorting)
  Coq -> T.concat (map coqBlock sorting)
  Caml -> T.concat (map camlBlock sorting)
  Lem -> T.concat (map lemBlock sorting)
  Twf -> T.concat (map twfBlock sorting)
  where
    opts = envOpts env
    twfBlock block =
      T.concat [h1 <> h2 <> h3 | (_, ((h1, h2, h3), _, _)) <- block]
        <> "\n"
        <> T.concat [s | (_, (_, s, _)) <- block]
        <> "\n"
    isaBlock block =
      (if optIsaPrimrec opts then "primrec\n" else "fun\n")
        <> T.intercalate "and " [h1 <> h2 <> h3 | (_, ((h1, h2, h3), _, _)) <- block]
        <> "where\n"
        <> T.intercalate "| " [s | (_, (_, s, _)) <- block]
        <> "\n"
        <> isaLemma block
    isaLemma block
      | any (\(_, (_, _, f)) -> isProj f) block =
          T.concat [p | (_, (_, _, FooterIsaProjLemma p _ _)) <- block]
            <> ( if optIsaGenerateLemmas opts
                   then
                     "lemma\n" <> T.concat [c | (_, (_, _, FooterIsaProjLemma _ c _)) <- block]
                       <> "  by(simp_all add: " <> T.unwords [defsOf f | (_, (_, _, f)) <- block] <> ")\n\n"
                   else ""
               )
      | otherwise = ""
    defsOf f = case f of
      FooterIsaProjLemma _ _ i -> i
      _ -> ""
    isProj f = case f of
      FooterIsaProjLemma {} -> True
      _ -> False
    holBlock block = case block of
      [] -> ""
      (nt, (_, _, f)) : _ ->
        let (define, proof) = case f of
              FooterProof s -> ("tDefine", "(" <> s <> ")")
              _ -> ("ottDefine", "")
         in "val _ = " <> define <> " \"" <> nt <> "\" `\n  " <> T.intercalate "/\\" [s | (_, (_, s, _)) <- block] <> "`" <> proof <> ";\n"
    coqBlock block = case block of
      [(nt, ((h1, h2, h3), s, _))]
        | nt `elem` refl -> "Fixpoint " <> h1 <> h2 <> h3 <> s <> "end.\n\n"
        | otherwise -> "Definition " <> h1 <> h3 <> s <> (if T.null h3 then ".\n\n" else "end.\n\n")
      _ -> "Fixpoint " <> T.intercalate "end\nwith " [h1 <> h2 <> h3 <> s | (_, ((h1, h2, h3), s, _)) <- block] <> "end.\n\n"
    camlBlock block = case block of
      [(nt, ((h1, h2, h3), s, _))]
        | nt `elem` refl -> "let rec " <> h1 <> h2 <> h3 <> s <> "\n\n"
        | otherwise -> "let " <> h1 <> h3 <> s <> "\n\n"
      _ -> "let rec " <> T.intercalate "and\n" [h1 <> h2 <> h3 <> s | (_, ((h1, h2, h3), s, _)) <- block] <> "\n\n"
    lemBlock block = case block of
      [(nt, ((h1, h2, h3), s, _))]
        | nt `elem` refl -> "let rec " <> h1 <> h2 <> h3 <> s <> "  end\n\n"
        | otherwise -> "let " <> h1 <> h3 <> s <> "  end\n\n"
      _ -> "let rec " <> T.intercalate "and\n" [h1 <> h2 <> h3 <> s <> "  end\n" | (_, ((h1, h2, h3), s, _)) <- block] <> "\n"

-- | Ott's @Dependency.compute@.
compute :: Env -> Collapsed -> P Text
compute env funcs = printFuncs env <$> sortFuncs funcs
