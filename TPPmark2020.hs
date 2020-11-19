{-# OPTIONS_GHC -Wall #-}
module TPPmark2020 where

import Control.Monad
import Control.Monad.ST
import Data.IntMap.Strict (IntMap)
import qualified Data.IntMap.Strict as IntMap
import Data.IntSet (IntSet)
import qualified Data.IntSet as IntSet
import Data.List
import Data.Maybe
import Data.Map.Strict (Map, (!))
import qualified Data.Map.Strict as Map
import System.Exit
import System.Process
import Text.Printf

import qualified ToySolver.SAT as SAT
import qualified ToySolver.SAT.Encoder.Cardinality as Card
import qualified ToySolver.SAT.Encoder.Tseitin as Tseitin
import qualified ToySolver.SAT.Store.CNF as SAT
import qualified ToySolver.FileFormat as FF
import qualified ToySolver.FileFormat.CNF as CNF

-- ------------------------------------------------------------------------
-- Utilities

pairs :: [a] -> [(a,a)]
pairs [] = []
pairs (x:ys) = [(x,y) | y <- ys] ++ pairs ys

parseQBFOutput :: String -> IntSet
parseQBFOutput s = IntSet.fromList [head $ map read $ words l' | l <- lines s, l' <- maybeToList (stripPrefix "V " l)]

readQBFOutput :: FilePath -> IO IntSet
readQBFOutput fname = do
  s <- readFile fname
  return $ parseQBFOutput s

-- ------------------------------------------------------------------------
-- Definition of the set {0, ±1, ±√2}

data Basis
  = One
  | Sqrt2
  deriving (Eq, Ord, Enum, Show)

data R
  = Zero
  | Signed Bool Basis
  deriving (Eq, Show)

showR :: R -> String
showR Zero = "0"
showR (Signed sign b) = (if sign then "" else "-") ++ showB b
  where
    showB One = "1"
    showB Sqrt2 = "√2"

instance Ord R where
  compare Zero Zero            = EQ
  compare Zero (Signed sign _) = if sign then LT else GT
  compare (Signed sign _) Zero = if sign then GT else LT
  compare (Signed sign1 b1) (Signed sign2 b2) =
    compare sign1 sign2 `mappend` (if sign1 then compare b1 b2 else compare b2 b1)

test_ord :: Bool
test_ord = and $ do
  (x, y) <- pairs vals
  return $ compare x y == LT && compare y x == GT

-- {0, ±1, ±√2}
vals :: [R]
vals = [Signed False Sqrt2, Signed False One, Zero, Signed True One, Signed True Sqrt2]

-- ------------------------------------------------------------------------
-- Definition of X = {0, ±1, ±√2}^n \ (0)_i∈{1,…,n}

type Point = [R]

showPoint :: Point -> String
showPoint xs = "(" ++ intercalate ", " (map showR xs) ++ ")"

points :: Int -> [Point]
points n = filter (zeros /=) $ replicateM n vals
  where
    zeros = replicate n Zero

-- ------------------------------------------------------------------------
-- Definition of orthogonality

orthogonal :: Point -> Point -> Bool
orthogonal p1 p2 = all (0==) $ Map.unionsWith (+) $ zipWith mul p1 p2
  where
    mul :: R -> R -> Map Basis Integer
    mul Zero _ = Map.empty
    mul _ Zero = Map.empty
    mul (Signed sign1 One) (Signed sign2 b2) = Map.singleton b2 (if sign1 == sign2 then 1 else -1)
    mul (Signed sign1 b1) (Signed sign2 One) = Map.singleton b1 (if sign1 == sign2 then 1 else -1)
    mul (Signed sign1 Sqrt2) (Signed sign2 Sqrt2) = Map.singleton One (if sign1 == sign2 then 2 else -2)

orthogonal_pairs :: [Point] -> [(Point, Point)]
orthogonal_pairs ps = [(p1, p2) | (p1, p2) <- pairs ps, orthogonal p1 p2]

orthogonal_tuples :: Int -> [Point] -> [[Point]]
orthogonal_tuples 0 _ = [[]]
orthogonal_tuples _ [] = []
orthogonal_tuples n (p:qs) = [[p] ++ rs | rs <- orthogonal_tuples (n-1) [q | q <- qs, orthogonal p q]] ++ orthogonal_tuples n qs

-- ------------------------------------------------------------------------
-- Q1.
-- 
-- Consider painting each element of the set X = {(x,y,z) | x,y,z ∈ {0,±1,±√2}}
-- \ {(0,0,0)} of 124 vectors white or black. Prove that the vectors cannot be
-- painted white or black in such a way that the following two conditions a)
-- and b) are met.
-- 
-- a) Whenever two of the vectors are orthogonal, at least one is black.
-- b) Whenever three of the vectors are mutually orthogonal, at least one is white.

solveQ1 :: IO ()
solveQ1 = do
  let n = 3

  db <- SAT.newCNFStore
  _isWhite <- encodeQ1 db n (points n)
  cnf <- SAT.getCNFFormula db
  FF.writeFile "Q1.cnf" cnf
  -- SAT solvers can easily decide the resulting CNF file to be UNSAT.

  -- Our SAT solver can also solve the problem.
  solver <- SAT.newSolver
  _isWhite <- encodeQ1 solver n (points n)
  ret <- SAT.solve solver
  print ret -- ⇒ False (= UNSAT)

encodeQ1 :: SAT.AddClause m db => db -> Int -> [Point] -> m (Map Point SAT.Var)
encodeQ1 db n points = do
  vs <- SAT.newVars db (length points)
  let isWhite :: Map Point SAT.Var
      isWhite = Map.fromList $ zip points vs
  -- a) Whenever two of the vectors are orthogonal, at least one is black.
  forM_ (orthogonal_pairs points) $ \(p1,p2) -> do
    SAT.addClause db [- (isWhite ! p1), - (isWhite ! p2)]
  -- b’) Whenever n vectors are mutually orthogonal, at least one is white.
  forM_ (orthogonal_tuples n points) $ \ps -> do
    SAT.addClause db [isWhite ! p | p <- ps]
  return isWhite

-- ------------------------------------------------------------------------
-- Some definitions for Q3.
--
-- Since Q2 is a special case of Q3, We'll prepare definition for Q3 first.

encodeQ3 :: Int -> [Point] -> Maybe Int -> (CNF.QDimacs, Map Point SAT.Var)
encodeQ3 n points ub = runST $ do
  db <- SAT.newCNFStore
  (isX, isWhite, vs) <- encodeQ3Matrix db n points
  tseitin <- Tseitin.newEncoder db
  card <- Card.newEncoderWithStrategy tseitin Card.Totalizer
  case ub of
    Nothing -> return ()
    Just ub' -> SAT.addAtMost card (Map.elems isX) ub'
  cnf <- SAT.getCNFFormula db
  let qdimacs =
        CNF.QDimacs
        { CNF.qdimacsNumVars    = CNF.cnfNumVars cnf
        , CNF.qdimacsNumClauses = CNF.cnfNumClauses cnf
        , CNF.qdimacsPrefix     = [(CNF.A, Map.elems isWhite), (CNF.E, vs)]
        , CNF.qdimacsMatrix     = CNF.cnfClauses cnf
        }
  return (qdimacs, isX)

encodeQ3Matrix :: SAT.AddClause m db => db -> Int -> [Point] -> m (Map Point SAT.Var, Map Point SAT.Var, [SAT.Var])
encodeQ3Matrix db n points = do
  vsX <- SAT.newVars db (length points)
  let isX :: Map Point SAT.Var
      isX = Map.fromList $ zip points vsX

  vsWhite <- SAT.newVars db (length points)
  let isWhite :: Map Point SAT.Var
      isWhite = Map.fromList $ zip points vsWhite

  flag <- SAT.newVar db

  -- c’) There exists at least one set of n vectors in the set that are mutually orthogonal to each other.
  vsT <- forM (orthogonal_tuples n points) $ \ps -> do
    v <- SAT.newVar db
    forM_ ps $ \p -> SAT.addClause db [-v, isX ! p]
    return (ps, v)
  SAT.addClause db (map snd vsT)

  -- flag → ¬a
  -- ¬a = (∃p,q∈X. p⊥q ∧ white(p) ∧ white(q))
  -- a) Whenever two of the vectors are orthogonal, at least one is black.
  vsNotA <- forM (orthogonal_pairs points) $ \(p1,p2) -> do
    -- v → (p1∈X ∧ p2∈X ∧ white(p1) ∧ white(p2))
    v <- SAT.newVar db
    SAT.addClause db [-v, isX ! p1]
    SAT.addClause db [-v, isX ! p2]
    SAT.addClause db [-v, isWhite ! p1]
    SAT.addClause db [-v, isWhite ! p2]
    return v
  SAT.addClause db (- flag : vsNotA)

  -- ¬flag → ¬b
  -- ¬b = (∃p∈X^n. "p are mutually orthogonal" ∧ (∀i. ¬white(p_i)))
  -- b’) Whenever n vectors are mutually orthogonal, at least one is white.
  vsNotB <- forM (orthogonal_tuples n points) $ \ps -> do
    -- v → ("p are mutually orthogonal" ∧ (∀i. ¬white(p_i)))
    v <- SAT.newVar db
    forM_ ps $ \p -> SAT.addClause db [-v, isX ! p]
    forM_ ps $ \p -> SAT.addClause db [-v, - (isWhite ! p)]
    return v
  SAT.addClause db (flag : vsNotB)

  return (isX, isWhite, flag : vsNotA ++ vsNotB)

encodeQ3GCNF :: Int -> [Point] -> (CNF.GCNF, Map Point Int)
encodeQ3GCNF n points = runST $ do
  db <- SAT.newCNFStore

  vsX <- SAT.newVars db (length points)
  let isX :: Map Point SAT.Var
      isX = Map.fromList $ zip points vsX

  vsWhite <- SAT.newVars db (length points)
  let isWhite :: Map Point SAT.Var
      isWhite = Map.fromList $ zip points vsWhite

  -- c’) There exists at least one set of n vectors in the set that are mutually orthogonal to each other.
  vsT <- forM (orthogonal_tuples n points) $ \ps -> do
    v <- SAT.newVar db
    forM_ ps $ \p -> SAT.addClause db [-v, isX ! p]
    return (ps, v)
  SAT.addClause db (map snd vsT)

  -- a) Whenever two of the vectors are orthogonal, at least one is black.
  forM_ (orthogonal_pairs points) $ \(p1,p2) -> do
    SAT.addClause db [- (isX ! p1), - (isX ! p2), - (isWhite ! p1), - (isWhite ! p2)]
  -- b’) Whenever n vectors are mutually orthogonal, at least one is white.
  forM_ (orthogonal_tuples n points) $ \ps -> do
    SAT.addClause db $ [- (isX ! p) | p <- ps] ++ [isWhite ! p | p <- ps]

  cnf <- SAT.getCNFFormula db
  let gcnf =
        CNF.GCNF
        { CNF.gcnfNumVars = CNF.cnfNumVars cnf
        , CNF.gcnfNumClauses = CNF.cnfNumClauses cnf + length points
        , CNF.gcnfLastGroupIndex = length points
        , CNF.gcnfClauses = [(0, c) | c <- CNF.cnfClauses cnf] ++ [(i, SAT.packClause [isX ! p]) | (i,p) <- zip [1..] points]
        }

  return (gcnf, Map.fromList (zip points [1..]))

-- ------------------------------------------------------------------------

solveQ2 :: IO ()
solveQ2 = do
  solveQ2' 33
{- ⇒
#X = 33
(-√2, -1, -1)
(-√2, -1, 0)
(-√2, -1, 1)
(-√2, 0, -√2)
(-√2, 0, -1)
(-√2, 0, 0)
(-√2, 1, -1)
(-√2, 1, 0)
(-1, -√2, 0)
(-1, -1, √2)
(-1, 0, -√2)
(-1, 0, 1)
(-1, 0, √2)
(-1, 1, -√2)
(-1, 1, √2)
(-1, √2, -1)
(0, -√2, -√2)
(0, -√2, -1)
(0, -√2, 1)
(0, -1, -√2)
(0, -1, 0)
(0, -1, 1)
(0, 0, 1)
(0, 1, -√2)
(1, -√2, -1)
(1, -√2, 0)
(1, 1, 0)
(1, 1, √2)
(1, √2, -1)
(1, √2, 1)
(√2, -√2, 0)
(√2, -1, -1)
(√2, 0, -1)
-}

  solveQ2' 32 -- Did not terminated within several hours.

solveQ2' :: Int -> IO ()
solveQ2' ub = do
  let (qdimacs, isX) = encodeQ3 3 (points 3) (Just ub)
      fname1 = "Q2_" ++ show ub ++ ".qdimacs"
      fname2 = "Q2_" ++ show ub ++ "_sol.txt"
  FF.writeFile fname1 qdimacs
  (exitCode, output, _err) <- readProcessWithExitCode "caqe" ["--qdo", fname1] ""
  writeFile fname2 output
  when (exitCode == ExitFailure 10) $ do -- SATISFIABLE
    let m = parseQBFOutput output
        points' = [x | (x, v) <- Map.toList isX, v `IntSet.member` m]
    putStrLn $ "#X = " ++ show (length points')
    forM_ points' $ \p -> do
      putStrLn (showPoint p)

solveQ2MUS :: IO ()
solveQ2MUS = do
  let n = 3
      (gcnf, m) = encodeQ3GCNF n (points n)
  FF.writeFile "Q2.gcnf" gcnf

  putStrLn "Group id to point mapping:"
  forM_ (Map.toList m) $ \(p, i) -> do
    putStrLn $ show i ++ ": " ++ showPoint p

  putStrLn ""

  -- q2MCSes are obtained using "toysat --all-mus --all-mus-method camus Q2.gcnf"
  let m2 = IntMap.fromList [(i, p) | (p, i) <- Map.toList m]
  if and [IntSet.null (IntSet.intersection s1 s2) | (s1,s2) <- pairs q2MCSes] then
    putStrLn "MCS are all disjoint"
  else
    undefined
  putStrLn "MCS:"
  forM_ (zip [(1::Int)..] q2MCSes) $ \(i, mcs) -> do
    putStrLn $ show i ++ ": " ++ intercalate ", " [showPoint (m2 IntMap.! j) | j <- IntSet.toList mcs]

  putStrLn ""
  printf "There are %d minimal solutions\n" $ product (map (toInteger . IntSet.size) q2MCSes)

q2MCSes
 :: [IntSet]
q2MCSes = map IntSet.fromList $
  [ [27, 98]
  , [41, 84]
  , [19, 106]
  , [17, 108]
  , [49, 76]
  , [35, 90]
  , [31, 94]
  , [29, 96]
  , [45, 80]
  , [7, 118]
  , [47, 78]
  , [9, 116]
  , [56, 69]
  , [28, 97]
  , [14, 111]
  , [40, 85]
  , [48, 77]
  , [18, 107]
  , [12, 113]
  , [60, 65]
  , [54, 71]
  , [52, 73]
  , [36, 89]
  , [8, 117]
  , [15, 39, 86, 110]
  , [53, 58, 67, 72]
  , [61, 62, 63, 64]
  , [23, 43, 82, 102]
  , [51, 57, 68, 74]
  , [3, 33, 92, 122]
  , [55, 59, 66, 70]
  , [11, 37, 88, 114]
  , [13, 38, 87, 112]
  ]

-- ------------------------------------------------------------------------

solveQ3 :: IO ()
solveQ3 = do
  let n = 4
  let (qdimacs, isX) = encodeQ3 n (points n) Nothing
      fname1 = "Q3_4.qdimacs"
      fname2 = "Q3_4_sol.txt"
  FF.writeFile fname1 qdimacs
  (exitCode, output, _err) <- readProcessWithExitCode "caqe" ["--qdo", fname1] ""
  writeFile fname2 output
  when (exitCode == ExitFailure 10) $ do -- SATISFIABLE
    let m = parseQBFOutput output
        points' = [x | (x, v) <- Map.toList isX, v `IntSet.member` m]
    putStrLn $ "#X = " ++ show (length points')
    forM_ points' $ \p -> do
      putStrLn (showPoint p)

-- ------------------------------------------------------------------------
