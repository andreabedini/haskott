-- | A model of the parts of ocamlgraph 2.2.0's @Graph.Pack.Digraph@ that
-- Ott uses to order its prover output: vertices, edges, strongly connected
-- components, topological folds and transitive closures.
--
-- Ott's output order follows the order in which ocamlgraph visits
-- vertices, so the model reproduces it. A vertex is identified by a tag
-- drawn from a counter that every graph of an Ott run shares; a graph keeps
-- its vertices in an OCaml @Hashtbl@ keyed by tag, whose iteration order is
-- by bucket (the tag modulo the number of buckets) and, within a bucket,
-- most recent first; the successors of a vertex are a set ordered by tag.
-- The counter is passed explicitly: every operation that creates vertices
-- takes the next free tag and returns the new one.
module Haskott.Graph
  ( Vertex (..)
  , Graph
  , create
  , newVertex
  , addVertex
  , addEdge
  , removeEdge
  , memEdge
  , vertices
  , succs
  , succsDecreasing
  , edges
  , sccList
  , topologicalFold
  , copyCount
  , transitiveSuccs
  ) where

import qualified Data.IntMap.Strict as IM
import qualified Data.IntSet as IS
import qualified Data.Map.Strict as M

-- | A vertex: its tag, unique in the run, and its label.
data Vertex = Vertex {vTag :: !Int, vLabel :: !Int}
  deriving (Show)

instance Eq Vertex where
  a == b = vTag a == vTag b

instance Ord Vertex where
  compare a b = compare (vTag a) (vTag b)

-- | An OCaml @Hashtbl@ from vertices: the buckets, each most recent
-- first, and the number of entries.
data Table v = Table
  { tBuckets :: !Int
  , tSize :: !Int
  , tData :: IM.IntMap [(Vertex, v)]
  }

-- | @Hashtbl.create n@: the number of buckets is the least power of two
-- at least @n@ and 16.
tableCreate :: Int -> Table v
tableCreate n = Table (power2Above 16 n) 0 IM.empty
  where
    power2Above x m = if x >= m then x else power2Above (x * 2) m

bucket :: Table v -> Vertex -> Int
bucket t v = vTag v `mod` tBuckets t

-- | @Hashtbl.replace@: in place when present, otherwise at the head of
-- the bucket, resizing when the table holds more than twice as many
-- entries as buckets.
tableReplace :: Vertex -> v -> Table v -> Table v
tableReplace k x t =
  let i = bucket t k
      cells = IM.findWithDefault [] i (tData t)
   in if any ((== k) . fst) cells
        then t {tData = IM.insert i [if k' == k then (k, x) else c | c@(k', _) <- cells] (tData t)}
        else
          let t' = t {tSize = tSize t + 1, tData = IM.insert i ((k, x) : cells) (tData t)}
           in if tSize t' > 2 * tBuckets t' then resize t' else t'

-- | Doubling the buckets keeps the order of the cells of each old
-- bucket in the new ones.
resize :: Table v -> Table v
resize t =
  let n = 2 * tBuckets t
      cells = tableToList t
      add m (k, x) = IM.insertWith (flip (++)) (vTag k `mod` n) [(k, x)] m
   in t {tBuckets = n, tData = foldl' add IM.empty cells}

tableLookup :: Vertex -> Table v -> Maybe v
tableLookup k t = lookup k (IM.findWithDefault [] (bucket t k) (tData t))

-- | The cells in @Hashtbl.iter@ order.
tableToList :: Table v -> [(Vertex, v)]
tableToList t = concat [IM.findWithDefault [] i (tData t) | i <- [0 .. tBuckets t - 1]]

-- | A directed graph: each vertex with its successors.
newtype Graph = Graph (Table (M.Map Vertex ()))

-- | @G.create ()@.
create :: Graph
create = Graph (tableCreate 97)

-- | @G.V.create label@, given the counter.
newVertex :: Int -> Int -> (Vertex, Int)
newVertex counter label = (Vertex (counter + 1) label, counter + 1)

addVertex :: Vertex -> Graph -> Graph
addVertex v g@(Graph t) = case tableLookup v t of
  Just _ -> g
  Nothing -> Graph (tableReplace v M.empty t)

addEdge :: Vertex -> Vertex -> Graph -> Graph
addEdge v1 v2 g =
  let Graph t = addVertex v2 (addVertex v1 g)
      s = maybe M.empty id (tableLookup v1 t)
   in Graph (tableReplace v1 (M.insert v2 () s) t)

removeEdge :: Vertex -> Vertex -> Graph -> Graph
removeEdge v1 v2 g@(Graph t) = case tableLookup v1 t of
  Nothing -> g
  Just s -> Graph (tableReplace v1 (M.delete v2 s) t)

memEdge :: Vertex -> Vertex -> Graph -> Bool
memEdge v1 v2 (Graph t) = maybe False (M.member v2) (tableLookup v1 t)

-- | The vertices in @G.iter_vertex@ order.
vertices :: Graph -> [Vertex]
vertices (Graph t) = map fst (tableToList t)

-- | The successors in @G.iter_succ@ order: increasing tags.
succs :: Graph -> Vertex -> [Vertex]
succs (Graph t) v = maybe [] M.keys (tableLookup v t)

-- | @G.succ@: decreasing tags.
succsDecreasing :: Graph -> Vertex -> [Vertex]
succsDecreasing g v = reverse (succs g v)

-- | The edges in @G.iter_edges@ order.
edges :: Graph -> [(Vertex, Vertex)]
edges g@(Graph t) = [(v, w) | (v, _) <- tableToList t, w <- succs g v]

-- | @Components.scc@: Tarjan's algorithm as ocamlgraph runs it, with an
-- explicit stack of actions; the number of components and the component
-- of each vertex.
scc :: Graph -> (Int, M.Map Vertex Int)
scc g = go (vertices g) (S M.empty M.empty [] 0 0 [])
  where
    go vs st = case vs of
      [] -> (numcomp st, hashcomp st)
      v : more -> go more (finish (visit v st))
    -- the continuation stack is threaded through visit and finish
    visit v st
      | M.member v (root st) = st {cont = cont st}
      | otherwise =
          let n = numdfs st + 1
              acts = foldl' (\c w -> Visit w : Test v w : c) (Finish v n : cont st) (succs g v)
           in st {numdfs = n, root = M.insert v n (root st), cont = acts}
    finish st = case cont st of
      [] -> st
      act : tl ->
        let st0 = st {cont = tl}
            st1 = case act of
              Finish v n ->
                if M.lookup v (root st0) == Just n
                  then
                    let hc = M.insert v (numcomp st0) (hashcomp st0)
                        (hc', rest) = pop n hc (numcomp st0) (stack st0)
                     in st0 {hashcomp = hc', stack = rest, numcomp = numcomp st0 + 1}
                  else st0 {stack = (n, v) : stack st0}
              Visit w -> visit w st0
              Test v w ->
                if M.member w (hashcomp st0)
                  then st0
                  else
                    let rv = root st0 M.! v
                        rw = root st0 M.! w
                     in st0 {root = M.insert v (min rv rw) (root st0)}
         in finish st1
    pop x hc c s = case s of
      (y, w) : l | y > x -> pop x (M.insert w c hc) c l
      _ -> (hc, s)

data S = S
  { root :: M.Map Vertex Int
  , hashcomp :: M.Map Vertex Int
  , stack :: [(Int, Vertex)]
  , numdfs :: !Int
  , numcomp :: !Int
  , cont :: [Action]
  }

data Action = Finish Vertex Int | Visit Vertex | Test Vertex Vertex

-- | @Components.scc_list@: the components in order, each its vertices in
-- reverse @iter_vertex@ order.
sccList :: Graph -> [[Vertex]]
sccList g =
  let (n, comp) = scc g
      arr = foldl' (\m v -> IM.insertWith (++) (comp M.! v) [v] m) IM.empty (vertices g)
   in [IM.findWithDefault [] i arr | i <- [0 .. n - 1]]

-- | @Topological.fold f g acc@.
topologicalFold :: (Vertex -> a -> a) -> Graph -> a -> a
topologicalFold f g acc0 =
  let (n, comp) = scc g
      ix = (comp M.!)
      step (vs, es, deg) x =
        let i = ix x
            vs' = IM.insertWith (++) i [x] vs
            (es', deg') =
              foldl'
                ( \(e, d) y ->
                    let j = ix y
                     in if i /= j then (IM.insertWith (++) i [j] e, IM.insertWith (+) j 1 d) else (e, d)
                )
                (es, deg)
                (succs g x)
         in (vs', es', deg')
      (vsA, esA, degA) = foldl' step (IM.empty, IM.empty, IM.empty) (vertices g)
      initial = [i | i <- [0 .. n - 1], IM.findWithDefault (0 :: Int) i degA == 0]
      walk queue deg acc = case queue of
        [] -> acc
        i : rest ->
          let acc' = foldr f acc (IM.findWithDefault [] i vsA)
              (queue', deg') =
                foldl'
                  ( \(q, d) j ->
                      let dj = IM.findWithDefault 0 j d
                       in if dj == 1 then (q ++ [j], d) else (q, IM.insert j (dj - 1) d)
                  )
                  (rest, deg)
                  (IM.findWithDefault [] i esA)
           in walk queue' deg' acc'
   in walk initial degA acc0

-- | The number of vertices @G.copy@ (and so @G.transitive_closure@)
-- creates.
copyCount :: Graph -> Int
copyCount = length . vertices

-- | The successors of each vertex in the transitive closure, as sets of
-- tags (the closure's own vertices are copies, matched back by label).
transitiveSuccs :: Graph -> M.Map Vertex IS.IntSet
transitiveSuccs g =
  let vs = vertices g
      direct = M.fromList [(v, IS.fromList (map vTag (succs g v))) | v <- vs]
      byTag = IM.fromList [(vTag v, v) | v <- vs]
      reach seen todo = case todo of
        [] -> seen
        t : more
          | IS.member t seen -> reach seen more
          | otherwise -> reach (IS.insert t seen) (IS.toList (direct M.! (byTag IM.! t)) ++ more)
   in M.fromList [(v, reach IS.empty (IS.toList (direct M.! v))) | v <- vs]
