{-# OPTIONS_GHC -Wall #-}
module Q2_MIP where

import Control.Monad
import Data.List
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map

-- ------------------------------------------------------------------------
-- Utilities

pairs :: [a] -> [(a,a)]
pairs [] = []
pairs (x:ys) = [(x,y) | y <- ys] ++ pairs ys

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

showR' :: R -> String
showR' Zero = "Zero"
showR' (Signed sign b) = (if sign then "" else "minus") ++ showB b
  where
    showB One = "One"
    showB Sqrt2 = "Root(2)"

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
showPoint xs = "(" ++ intercalate "," (map showR xs) ++ ")"

showPoint' :: Point -> String
showPoint' xs = "(" ++ intercalate "," (map showR' xs) ++ ")"

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

printQ2MIP :: Bool -> IO ()
printQ2MIP useUnicode = do
  let n = 3
      ps = points n
      isX p = if useUnicode then "x" ++ showPoint p else "x" ++ showPoint' p
      c i = "c(" ++ show i ++ ")"

      mcses :: [[Point]]
      mcses =
        [ [[Zero, Signed False One, Signed False Sqrt2], [Zero, Signed True One, Signed True Sqrt2]]
        , [[Signed False Sqrt2, Zero, Signed False One], [Signed True Sqrt2, Zero, Signed True One]]
        , [[Signed False One, Signed True Sqrt2, Signed True One], [Signed True One, Signed False Sqrt2, Signed False One]]
        , [[Signed False Sqrt2, Signed False One, Zero], [Signed True Sqrt2, Signed True One, Zero]]
        , [[Signed False One, Signed True Sqrt2, Signed False One], [Signed True One, Signed False Sqrt2, Signed True One]]
        , [[Signed False One, Signed True One, Signed False Sqrt2], [Signed True One, Signed False One, Signed True Sqrt2]]
        , [[Signed False One, Signed False Sqrt2, Signed True One], [Signed True One, Signed True Sqrt2, Signed False One]]
        , [[Signed False One, Signed True One, Signed True Sqrt2], [Signed True One, Signed False One, Signed False Sqrt2]]
        , [[Signed False Sqrt2, Signed False One, Signed False One], [Signed True Sqrt2, Signed True One, Signed True One]]
        , [[Signed False One, Signed False One, Signed False Sqrt2], [Signed True One, Signed True One, Signed True Sqrt2]]
        , [[Signed False One, Signed False Sqrt2, Signed False One], [Signed True One, Signed True Sqrt2, Signed True One]]
        , [[Signed False One, Signed False One, Signed True Sqrt2], [Signed True One, Signed True One, Signed False Sqrt2]]
        , [[Signed False Sqrt2, Signed True One, Signed True One], [Signed True Sqrt2, Signed False One, Signed False One]]
        , [[Signed False Sqrt2, Signed False One, Signed True One], [Signed True Sqrt2, Signed True One, Signed False One]]
        , [[Zero, Signed False Sqrt2, Signed False One], [Zero, Signed True Sqrt2, Signed True One]]
        , [[Zero, Signed False Sqrt2, Signed True One], [Zero, Signed True Sqrt2, Signed False One]]
        , [[Signed False Sqrt2, Signed True One, Signed False One], [Signed True Sqrt2, Signed False One, Signed True One]]
        , [[Signed False One, Signed True Sqrt2, Zero], [Signed True One, Signed False Sqrt2, Zero]]
        , [[Signed False One, Zero, Signed True Sqrt2], [Signed True One, Zero, Signed False Sqrt2]]
        , [[Signed False One, Zero, Signed False Sqrt2], [Signed True One, Zero, Signed True Sqrt2]]
        , [[Signed False Sqrt2, Zero, Signed True One], [Signed True Sqrt2, Zero, Signed False One]]
        , [[Zero, Signed False One, Signed True Sqrt2], [Zero, Signed True One, Signed False Sqrt2]]
        , [[Signed False Sqrt2, Signed True One, Zero], [Signed True Sqrt2, Signed False One, Zero]]
        , [[Signed False One, Signed False Sqrt2, Zero], [Signed True One, Signed True Sqrt2, Zero]]
        , [[Zero, Zero, Signed False Sqrt2], [Zero, Zero, Signed False One], [Zero, Zero, Signed True One], [Zero, Zero, Signed True Sqrt2]]
        , [[Zero, Signed False Sqrt2, Zero], [Zero, Signed False One, Zero], [Zero, Signed True One, Zero], [Zero, Signed True Sqrt2, Zero]]
        , [[Signed False Sqrt2, Zero, Signed True Sqrt2], [Signed False One, Zero, Signed True One], [Signed True One, Zero, Signed False One], [Signed True Sqrt2, Zero, Signed False Sqrt2]]
        , [[Signed False Sqrt2, Zero, Zero], [Signed False One, Zero, Zero], [Signed True One, Zero, Zero], [Signed True Sqrt2, Zero, Zero]]
        , [[Signed False Sqrt2, Zero, Signed False Sqrt2], [Signed False One, Zero, Signed False One], [Signed True One, Zero, Signed True One], [Signed True Sqrt2, Zero, Signed True Sqrt2]]
        , [[Signed False Sqrt2, Signed True Sqrt2, Zero], [Signed False One, Signed True One, Zero], [Signed True One, Signed False One, Zero], [Signed True Sqrt2, Signed False Sqrt2, Zero]]
        , [[Zero, Signed False Sqrt2, Signed False Sqrt2], [Zero, Signed False One, Signed False One], [Zero, Signed True One, Signed True One], [Zero, Signed True Sqrt2, Signed True Sqrt2]]
        , [[Signed False Sqrt2, Signed False Sqrt2, Zero], [Signed False One, Signed False One, Zero], [Signed True One, Signed True One, Zero], [Signed True Sqrt2, Signed True Sqrt2, Zero]]
        , [[Zero, Signed False Sqrt2, Signed True Sqrt2], [Zero, Signed False One, Signed True One], [Zero, Signed True One, Signed False One], [Zero, Signed True Sqrt2, Signed False Sqrt2]]
        ]

  putStrLn "minimize"
  putStrLn $ intercalate " + " [isX p | p <- ps]
  putStrLn "subject to"
  cs <- forM (zip [(0::Int)..] (orthogonal_tuples n ps)) $ \(i, ps) -> do
    forM_ ps $ \p -> do
      putStrLn $ "- " ++ c i ++ " + " ++ isX p ++ " >= 0"
    return (c i)
  putStrLn $ intercalate " + " cs ++ " >= 1"
  forM_ mcses $ \mcs -> do
    putStrLn $ intercalate " + " [isX p | p <- mcs] ++ " >= 1"
  putStrLn "binary"
  putStrLn $ intercalate " " ([isX p | p <- ps] ++ cs)
  putStrLn "end"

-- ------------------------------------------------------------------------
