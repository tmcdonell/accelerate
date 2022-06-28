{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators       #-}
-- |
-- Module      : Data.Array.Accelerate.Test.NoFib.Issues.Issue137
-- Copyright   : [2009..2020] The Accelerate Team
-- License     : BSD3
--
-- Maintainer  : Trevor L. McDonell <trevor.mcdonell@gmail.com>
-- Stability   : experimental
-- Portability : non-portable (GHC extensions)
--
-- https://github.com/AccelerateHS/accelerate/issues/137
--

module Data.Array.Accelerate.Test.NoFib.Issues.Issue137 (

  test_issue137

) where

import Data.Array.Accelerate                                        as A
import Data.Array.Accelerate.Test.NoFib.Base

import Test.Tasty
import Test.Tasty.HUnit
import Prelude                                                      hiding ( Maybe(..) )


test_issue137 :: RunN -> TestTree
test_issue137 runN =
  testCase "137"  $ ref1 @=? runN test1


ref1 :: Vector (Int,Int)
ref1 = fromList (Z:.384) [(1,2),(0,1),(2,3),(0,1),(3,4),(0,1),(4,5),(0,1),(5,5),(0,1),(4,5),(0,1),(3,4),(0,1),(2,3),(0,1),(1,2),(1,2),(0,1),(2,3),(0,1),(3,4),(0,1),(4,5),(0,1),(5,5),(0,1),(4,5),(0,1),(3,4),(0,1),(2,3),(0,1),(1,2),(1,2),(0,1),(2,3),(0,1),(3,4),(0,1),(4,5),(0,1),(5,5),(0,1),(4,5),(0,1),(3,4),(0,1),(2,3),(0,1),(1,2),(1,2),(0,1),(2,3),(0,1),(3,4),(0,1),(4,5),(0,1),(5,5),(0,1),(4,5),(0,1),(3,4),(0,1),(2,3),(0,1),(1,2),(1,2),(0,1),(2,3),(0,1),(3,4),(0,1),(4,5),(0,1),(5,5),(0,1),(4,5),(0,1),(3,4),(0,1),(2,3),(0,1),(1,2),(1,2),(0,1),(2,3),(0,1),(3,4),(0,1),(4,5),(0,1),(5,5),(0,1),(4,5),(0,1),(3,4),(0,1),(2,3),(0,1),(1,2),(1,2),(0,1),(2,3),(0,1),(3,4),(0,1),(4,5),(0,1),(5,5),(0,1),(4,5),(0,1),(3,4),(0,1),(2,3),(0,1),(1,2),(1,2),(0,1),(2,3),(0,1),(3,4),(0,1),(4,5),(0,1),(5,5),(0,1),(4,5),(0,1),(3,4),(0,1),(2,3),(0,1),(1,2),(1,2),(0,1),(2,3),(0,1),(3,4),(0,1),(4,5),(0,1),(5,5),(0,1),(4,5),(0,1),(3,4),(0,1),(2,3),(0,1),(1,2),(1,2),(0,1),(2,3),(0,1),(3,4),(0,1),(4,5),(0,1),(5,5),(0,1),(4,5),(0,1),(3,4),(0,1),(2,3),(0,1),(1,2),(1,2),(0,1),(2,3),(0,1),(3,4),(0,1),(4,5),(0,1),(5,5),(0,1),(4,5),(0,1),(3,4),(0,1),(2,3),(0,1),(1,2),(1,2),(0,1),(2,3),(0,1),(3,4),(0,1),(4,5),(0,1),(5,5),(0,1),(4,5),(0,1),(3,4),(0,1),(2,3),(0,1),(1,2),(1,2),(0,1),(2,3),(0,1),(3,4),(0,1),(4,5),(0,1),(5,5),(0,1),(4,5),(0,1),(3,4),(0,1),(2,3),(0,1),(1,2),(1,2),(0,1),(2,3),(0,1),(3,4),(0,1),(4,5),(0,1),(5,5),(0,1),(4,5),(0,1),(3,4),(0,1),(2,3),(0,1),(1,2),(1,2),(0,1),(2,3),(0,1),(3,4),(0,1),(4,5),(0,1),(5,5),(0,1),(4,5),(0,1),(3,4),(0,1),(2,3),(0,1),(1,2),(1,2),(0,1),(2,3),(0,1),(3,4),(0,1),(4,5),(0,1),(5,5),(0,1),(4,5),(0,1),(3,4),(0,1),(2,3),(0,1),(1,2),(1,2),(0,1),(2,3),(0,1),(3,4),(0,1),(4,5),(0,1),(5,5),(0,1),(4,5),(0,1),(3,4),(0,1),(2,3),(0,1),(1,2),(1,2),(0,1),(2,3),(0,1),(3,4),(0,1),(4,5),(0,1),(5,5),(0,1),(4,5),(0,1),(3,4),(0,1),(2,3),(0,1),(1,2),(1,2),(0,1),(2,3),(0,1),(3,4),(0,1),(4,5),(0,1),(5,5),(0,1),(4,5),(0,1),(3,4),(0,1),(2,3),(0,1),(1,2),(1,2),(0,1),(2,3),(0,1),(3,4),(0,1),(4,5),(0,1),(5,5),(0,1),(4,5),(0,1),(3,4),(0,1),(2,3),(0,1),(1,2),(1,2),(0,1),(2,3),(0,1),(3,4),(0,1),(4,5),(0,1),(5,5),(0,1),(4,5),(0,1),(3,4),(0,1),(2,3),(0,1),(1,2),(1,2),(0,1),(2,3),(0,1),(3,4),(0,1),(4,5),(0,1),(5,5),(0,1),(4,5),(0,1),(3,4),(0,1),(2,3),(0,1),(1,2),(1,2),(0,10000),(10000,10000),(10000,10000),(10000,10000),(10000,10000),(10000,10000),(10000,10000),(10000,10000),(10000,10000)]

test1 :: Acc (Vector (Int,Int))
test1 =
  let
      sz          = 3000 :: Int
      interm_arrA = use $ A.fromList (Z :. sz) [ 8 - (a `mod` 17) | a <- [1..sz]] :: Acc (Vector Int)
      msA         = use $ A.fromList (Z :. sz) [ (a `div` 8) | a <- [1..sz]]
      inf         = 10000 :: Exp Int
      infsA       = A.generate (index1 (384 :: Exp Int)) (\_ -> T2 inf inf)
      inpA        = A.map (\v -> T2 (abs v) inf) interm_arrA
  in
  A.permute (\a12 b12 -> let T2 a1 a2 = a12
                             T2 b1 b2 = b12
                         in (a1 A.<= b1)
                          ? ( T2 a1 (A.min a2 b1)
                            , T2 b1 (A.min b2 a1)
                            ))
            infsA
            (\ix -> Just (index1 (msA A.! ix)))
            inpA

