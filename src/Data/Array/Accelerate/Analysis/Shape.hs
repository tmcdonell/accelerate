{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE CPP                 #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE PatternGuards       #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE RecordWildCards     #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications    #-}
{-# OPTIONS_HADDOCK hide #-}
-- |
-- Module      : Data.Array.Accelerate.Analysis.Shape
-- Copyright   : [2008..2019] The Accelerate Team
-- License     : BSD3
--
-- Maintainer  : Trevor L. McDonell <trevor.mcdonell@gmail.com>
-- Stability   : experimental
-- Portability : non-portable (GHC extensions)
--

module Data.Array.Accelerate.Analysis.Shape (

  -- * query AST dimensionality
  AccDim, accDim, delayedDim, preAccDim,
  expDim,

) where

-- friends
import Data.Array.Accelerate.AST
import Data.Array.Accelerate.Type
import Data.Array.Accelerate.Trafo.Base
import Data.Array.Accelerate.Array.Sugar


type AccDim acc  = forall aenv sh e. acc aenv (Array sh e) -> Int

-- |Reify the dimensionality of the result type of an array computation
--
accDim :: AccDim OpenAcc
accDim (OpenAcc acc) = preAccDim accDim acc

delayedDim :: AccDim DelayedOpenAcc
delayedDim (Manifest acc)   = preAccDim delayedDim acc
delayedDim (Delayed sh _ _) = expDim sh


-- |Reify dimensionality of a computation parameterised over a recursive closure
--
preAccDim :: forall acc aenv sh e. AccDim acc -> PreOpenAcc acc aenv (Array sh e) -> Int
preAccDim k pacc =
  case pacc of
    Alet _ acc           -> k acc
    Avar{}               -> case arrays @(Array sh e) of
                              ArraysRarray -> rank @sh
#if __GLASGOW_HASKELL__ < 800
                              _            -> error "halt, fiend!"
#endif

    Apply{}              -> case arrays @(Array sh e) of
                              ArraysRarray -> rank @sh
#if __GLASGOW_HASKELL__ < 800
                              _            -> error "umm, hello"
#endif

    Aforeign{}          -> case arrays @(Array sh e) of
                              ArraysRarray -> rank @sh
#if __GLASGOW_HASKELL__ < 800
                              _            -> error "I don't even like snails!"
#endif

    Atuple{}             -> case arrays @(Array sh e) of
                              ArraysRarray -> rank @sh
#if __GLASGOW_HASKELL__ < 800
                              _            -> error "can we keep him?"
#endif

    Aprj{}               -> case arrays @(Array sh e) of
                              ArraysRarray -> rank @sh
#if __GLASGOW_HASKELL__ < 800
                              _            -> error "inconceivable!"
#endif

    Collect{}            -> case arrays @(Array sh e) of
                              ArraysRarray -> ndim (eltType @sh)

    Subarray{}           -> ndim (eltType @sh)

    Use{}                -> case arrays @(Array sh e) of
                              ArraysRarray -> rank @sh
#if __GLASGOW_HASKELL__ < 800
                              _            -> error "ppbbbbbt~"
#endif

    Acond _ acc _        -> k acc
    Awhile _ _ acc       -> k acc
    Unit _               -> 0
    Generate _ _         -> rank @sh
    Transform _ _ _ _    -> rank @sh
    Reshape _ _          -> rank @sh
    Replicate _ _ _      -> rank @sh
    Slice _ _ _          -> rank @sh
    Map _ acc            -> k acc
    ZipWith _ _ acc      -> k acc
    Fold _ _ acc         -> k acc - 1
    Fold1 _ acc          -> k acc - 1
    FoldSeg _ _ acc _    -> k acc
    Fold1Seg _ acc _     -> k acc
    Scanl _ _ acc        -> k acc
    Scanl1 _ acc         -> k acc
    Scanr _ _ acc        -> k acc
    Scanr1 _ acc         -> k acc
    Permute _ acc _ _    -> k acc
    Backpermute _ _ _    -> rank @sh
    Stencil _ _ acc      -> k acc
    Stencil2 _ _ acc _ _ -> k acc


-- |Reify dimensionality of a scalar expression yielding a shape
--
expDim :: forall acc env aenv sh. Elt sh => PreOpenExp acc env aenv sh -> Int
expDim _ = ndim (eltType @sh)


-- Count the number of components to a tuple type
--
ndim :: TupleType a -> Int
ndim TypeRunit       = 0
ndim TypeRscalar{}   = 1
ndim (TypeRpair a b) = ndim a + ndim b

