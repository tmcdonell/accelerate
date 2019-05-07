{-# LANGUAGE CPP                 #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE FlexibleInstances   #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE PatternGuards       #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell     #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE TypeOperators       #-}
{-# LANGUAGE ViewPatterns        #-}
-- |
-- Module      : Data.Array.Accelerate.Trafo.Shrink
-- Copyright   : [2012..2019] The Accelerate Team
-- License     : BSD3
--
-- Maintainer  : Trevor L. McDonell <trevor.mcdonell@gmail.com>
-- Stability   : experimental
-- Portability : non-portable (GHC extensions)
--
-- The shrinking substitution arises as a restriction of beta-reduction to cases
-- where the bound variable is used zero (dead-code elimination) or one (linear
-- inlining) times. By simplifying terms, the shrinking reduction can expose
-- opportunities for further optimisation.
--
-- TODO: replace with a linear shrinking algorithm; e.g.
--
--   * Andrew Appel & Trevor Jim, "Shrinking lambda expressions in linear time".
--
--   * Nick Benton, Andrew Kennedy, Sam Lindley and Claudio Russo, "Shrinking
--     Reductions in SML.NET"
--

module Data.Array.Accelerate.Trafo.Shrink (

  -- Shrinking
  Shrink(..),
  ShrinkAcc, shrinkPreAcc,

) where

-- standard library
import Data.Monoid                                      hiding ( Last )
import Control.Applicative                              hiding ( Const )
import Prelude                                          hiding ( all, exp, seq )

-- friends
import Data.Array.Accelerate.AST
import Data.Array.Accelerate.Array.Sugar               hiding ( Any )
import Data.Array.Accelerate.Trafo.Base
import Data.Array.Accelerate.Trafo.Occurrence
import Data.Array.Accelerate.Trafo.Substitution

import qualified Data.Array.Accelerate.Debug.Stats      as Stats


class Shrink f where
  shrink  :: f -> f
  shrink' :: f -> (Bool, f)

  shrink = snd . shrink'

instance Kit acc => Shrink (PreOpenExp acc env aenv e) where
  shrink' = shrinkExp

instance Kit acc => Shrink (PreOpenFun acc env aenv f) where
  shrink' = shrinkFun


-- The shrinking substitution for scalar expressions. This is a restricted
-- instance of beta-reduction to cases where the bound variable is used zero
-- (dead-code elimination) or one (linear inlining) times.
--
shrinkExp :: Kit acc => PreOpenExp acc env aenv t -> (Bool, PreOpenExp acc env aenv t)
shrinkExp = Stats.substitution "shrink exp" . first getAny . shrinkE
  where
    -- If the bound variable is used at most this many times, it will be inlined
    -- into the body. In cases where it is not used at all, this is equivalent
    -- to dead-code elimination.
    --
    lIMIT :: Int
    lIMIT = 1

    shrinkE :: Kit acc => PreOpenExp acc env aenv t -> (Any, PreOpenExp acc env aenv t)
    shrinkE exp = case exp of
      Let bnd body
        | Var _ <- bnd          -> Stats.inline "Var"   . yes $ shrinkE (inline body bnd)
        | allE (<= lIMIT) uses  -> Stats.betaReduce msg . yes $ shrinkE (inline (snd body') (snd bnd'))
        | otherwise             -> Let <$> bnd' <*> body'
        where
          bnd'  = shrinkE bnd
          body' = shrinkE body
          uses  = usesOfExp ZeroIdx (snd body')

          msg   = if allE (== 0) uses
                    then "dead exp"
                    else "inline exp"   -- forced inlining when lIMIT > 1
      --
      Var idx                   -> pure (Var idx)
      Const c                   -> pure (Const c)
      Undef                     -> pure Undef
      Tuple t                   -> Tuple <$> shrinkT t
      Prj tup e                 -> Prj tup <$> shrinkE e
      IndexAny                  -> pure IndexAny
      IndexNil                  -> pure IndexNil
      IndexCons sl sz           -> IndexCons <$> shrinkE sl <*> shrinkE sz
      IndexHead sh              -> IndexHead <$> shrinkE sh
      IndexTail sh              -> IndexTail <$> shrinkE sh
      IndexTrans sh             -> IndexTrans <$> shrinkE sh
      IndexSlice x ix sh        -> IndexSlice x <$> shrinkE ix <*> shrinkE sh
      IndexFull x ix sl         -> IndexFull x <$> shrinkE ix <*> shrinkE sl
      FromIndex sh i            -> FromIndex <$> shrinkE sh <*> shrinkE i
      ToIndex sh ix             -> ToIndex <$> shrinkE sh <*> shrinkE ix
      ToSlice x sh i            -> ToSlice x <$> shrinkE sh <*> shrinkE i
      Cond p t e                -> Cond <$> shrinkE p <*> shrinkE t <*> shrinkE e
      While p f x               -> While <$> shrinkF p <*> shrinkF f <*> shrinkE x
      PrimConst c               -> pure (PrimConst c)
      PrimApp f x               -> PrimApp f <$> shrinkE x
      Index a sh                -> Index a <$> shrinkE sh
      LinearIndex a i           -> LinearIndex a <$> shrinkE i
      Shape a                   -> pure (Shape a)
      ShapeSize sh              -> ShapeSize <$> shrinkE sh
      Intersect sh sz           -> Intersect <$> shrinkE sh <*> shrinkE sz
      Union sh sz               -> Union <$> shrinkE sh <*> shrinkE sz
      Foreign ff f e            -> Foreign ff <$> shrinkF f <*> shrinkE e
      Coerce e                  -> Coerce <$> shrinkE e

    shrinkT :: Kit acc => Tuple (PreOpenExp acc env aenv) t -> (Any, Tuple (PreOpenExp acc env aenv) t)
    shrinkT NilTup        = pure NilTup
    shrinkT (SnocTup t e) = SnocTup <$> shrinkT t <*> shrinkE e

    shrinkF :: Kit acc => PreOpenFun acc env aenv t -> (Any, PreOpenFun acc env aenv t)
    shrinkF = first Any . shrinkFun

    first :: (a -> a') -> (a,b) -> (a',b)
    first f (x,y) = (f x, y)

    yes :: (Any, x) -> (Any, x)
    yes (_, x) = (Any True, x)

shrinkFun :: Kit acc => PreOpenFun acc env aenv f -> (Bool, PreOpenFun acc env aenv f)
shrinkFun (Lam f)  = Lam  <$> shrinkFun f
shrinkFun (Body b) = Body <$> shrinkExp b


-- The shrinking substitution for array computations. This is further limited to
-- dead-code elimination only, primarily because linear inlining may inline
-- array computations into scalar expressions, which is generally not desirable.
--
type ShrinkAcc acc = forall aenv a.   acc aenv a -> acc aenv a
type ReduceAcc acc = forall aenv s t. Arrays s => acc aenv s -> acc (aenv,s) t -> Maybe (PreOpenAcc acc aenv t)

shrinkPreAcc
    :: forall acc aenv arrs.
       ShrinkAcc acc
    -> ReduceAcc acc
    -> PreOpenAcc acc aenv arrs
    -> PreOpenAcc acc aenv arrs
shrinkPreAcc shrinkAcc reduceAcc = Stats.substitution "shrink acc" shrinkA
  where
    shrinkA :: PreOpenAcc acc aenv' a -> PreOpenAcc acc aenv' a
    shrinkA pacc = case pacc of
      Alet bnd body
        | Just reduct <- reduceAcc bnd' body'   -> shrinkA reduct
        | otherwise                             -> Alet bnd' body'
        where
          bnd'  = shrinkAcc bnd
          body' = shrinkAcc body
      --
      Avar ix                   -> Avar ix
      Atuple tup                -> Atuple (shrinkAT tup)
      Aprj tup a                -> Aprj tup (shrinkAcc a)
      Apply f a                 -> Apply (shrinkAF f) (shrinkAcc a)
      Aforeign ff af a          -> Aforeign ff af (shrinkAcc a)
      Acond p t e               -> Acond (shrinkE p) (shrinkAcc t) (shrinkAcc e)
      Awhile p f a              -> Awhile (shrinkAF p) (shrinkAF f) (shrinkAcc a)
      Use a                     -> Use a
      Subarray ix sh a          -> Subarray (shrinkE ix) (shrinkE sh) a
      Unit e                    -> Unit (shrinkE e)
      Reshape e a               -> Reshape (shrinkE e) (shrinkAcc a)
      Generate e f              -> Generate (shrinkE e) (shrinkF f)
      Transform sh ix f a       -> Transform (shrinkE sh) (shrinkF ix) (shrinkF f) (shrinkAcc a)
      Replicate sl slix a       -> Replicate sl (shrinkE slix) (shrinkAcc a)
      Slice sl a slix           -> Slice sl (shrinkAcc a) (shrinkE slix)
      Map f a                   -> Map (shrinkF f) (shrinkAcc a)
      ZipWith f a1 a2           -> ZipWith (shrinkF f) (shrinkAcc a1) (shrinkAcc a2)
      Fold f z a                -> Fold (shrinkF f) (shrinkE z) (shrinkAcc a)
      Fold1 f a                 -> Fold1 (shrinkF f) (shrinkAcc a)
      FoldSeg f z a b           -> FoldSeg (shrinkF f) (shrinkE z) (shrinkAcc a) (shrinkAcc b)
      Fold1Seg f a b            -> Fold1Seg (shrinkF f) (shrinkAcc a) (shrinkAcc b)
      Scanl f z a               -> Scanl (shrinkF f) (shrinkE z) (shrinkAcc a)
      Scanl' f z a              -> Scanl' (shrinkF f) (shrinkE z) (shrinkAcc a)
      Scanl1 f a                -> Scanl1 (shrinkF f) (shrinkAcc a)
      Scanr f z a               -> Scanr (shrinkF f) (shrinkE z) (shrinkAcc a)
      Scanr' f z a              -> Scanr' (shrinkF f) (shrinkE z) (shrinkAcc a)
      Scanr1 f a                -> Scanr1 (shrinkF f) (shrinkAcc a)
      Permute f1 a1 f2 a2       -> Permute (shrinkF f1) (shrinkAcc a1) (shrinkF f2) (shrinkAcc a2)
      Backpermute sh f a        -> Backpermute (shrinkE sh) (shrinkF f) (shrinkAcc a)
      Stencil f b a             -> Stencil (shrinkF f) (shrinkB b) (shrinkAcc a)
      Stencil2 f b1 a1 b2 a2    -> Stencil2 (shrinkF f) (shrinkB b1) (shrinkAcc a1) (shrinkB b2) (shrinkAcc a2)
      Collect si u v i s        -> Collect si (shrinkE u) (shrinkE <$> v) (shrinkE <$> i) (shrinkS s)

    shrinkS :: PreOpenSeq index acc aenv' a -> PreOpenSeq index acc aenv' a
    shrinkS seq =
      case seq of
        Producer p s -> Producer (shrinkP p) (shrinkS s)
        Consumer c   -> Consumer (shrinkC c)
        Reify ty a   -> Reify ty (shrinkAcc a)

    shrinkP :: Producer index acc aenv' a -> Producer index acc aenv' a
    shrinkP p =
      case p of
        Pull src            -> Pull src
        Subarrays sh arr    -> Subarrays (shrinkE sh) arr
        FromSegs s n vs     -> FromSegs (shrinkAcc s) (shrinkE n) (shrinkAcc vs)
        Produce l f         -> Produce (shrinkE <$> l) (shrinkAF f)
        -- MapBatch f c c' a x -> MapBatch (shrinkAF f) (shrinkAF c) (shrinkAF c') (shrinkAcc a) (shrinkAcc x)
        ProduceAccum l f a  -> ProduceAccum (shrinkE <$> l) (shrinkAF f) (shrinkAcc a)

    shrinkC :: Consumer index acc aenv' a -> Consumer index acc aenv' a
    shrinkC c =
      case c of
        FoldBatch f a x -> FoldBatch (shrinkAF f) (shrinkAcc a) (shrinkAcc x)
        Last a d        -> Last (shrinkAcc a) (shrinkAcc d)
        Elements x      -> Elements (shrinkAcc x)
        Tabulate x      -> Tabulate (shrinkAcc x)
        Stuple t        -> Stuple (shrinkCT t)

    shrinkCT :: Atuple (PreOpenSeq index acc aenv') t -> Atuple (PreOpenSeq index acc aenv') t
    shrinkCT NilAtup        = NilAtup
    shrinkCT (SnocAtup t c) = SnocAtup (shrinkCT t) (shrinkS c)

    shrinkE :: PreOpenExp acc env aenv' t -> PreOpenExp acc env aenv' t
    shrinkE exp = case exp of
      Let bnd body              -> Let (shrinkE bnd) (shrinkE body)
      Var idx                   -> Var idx
      Const c                   -> Const c
      Undef                     -> Undef
      Tuple t                   -> Tuple (shrinkT t)
      Prj tup e                 -> Prj tup (shrinkE e)
      IndexAny                  -> IndexAny
      IndexNil                  -> IndexNil
      IndexCons sl sz           -> IndexCons (shrinkE sl) (shrinkE sz)
      IndexHead sh              -> IndexHead (shrinkE sh)
      IndexTail sh              -> IndexTail (shrinkE sh)
      IndexTrans sh             -> IndexTrans (shrinkE sh)
      IndexSlice x ix sh        -> IndexSlice x (shrinkE ix) (shrinkE sh)
      IndexFull x ix sl         -> IndexFull x (shrinkE ix) (shrinkE sl)
      ToSlice x sh i            -> ToSlice x (shrinkE sh) (shrinkE i)
      ToIndex sh ix             -> ToIndex (shrinkE sh) (shrinkE ix)
      FromIndex sh i            -> FromIndex (shrinkE sh) (shrinkE i)
      Cond p t e                -> Cond (shrinkE p) (shrinkE t) (shrinkE e)
      While p f x               -> While (shrinkF p) (shrinkF f) (shrinkE x)
      PrimConst c               -> PrimConst c
      PrimApp f x               -> PrimApp f (shrinkE x)
      Index a sh                -> Index (shrinkAcc a) (shrinkE sh)
      LinearIndex a i           -> LinearIndex (shrinkAcc a) (shrinkE i)
      Shape a                   -> Shape (shrinkAcc a)
      ShapeSize sh              -> ShapeSize (shrinkE sh)
      Intersect sh sz           -> Intersect (shrinkE sh) (shrinkE sz)
      Union sh sz               -> Union (shrinkE sh) (shrinkE sz)
      Foreign ff f e            -> Foreign ff (shrinkF f) (shrinkE e)
      Coerce e                  -> Coerce (shrinkE e)

    shrinkF :: PreOpenFun acc env aenv' f -> PreOpenFun acc env aenv' f
    shrinkF (Lam f)  = Lam (shrinkF f)
    shrinkF (Body b) = Body (shrinkE b)

    shrinkT :: Tuple (PreOpenExp acc env aenv') t -> Tuple (PreOpenExp acc env aenv') t
    shrinkT NilTup        = NilTup
    shrinkT (SnocTup t e) = shrinkT t `SnocTup` shrinkE e

    shrinkAT :: Atuple (acc aenv') t -> Atuple (acc aenv') t
    shrinkAT NilAtup        = NilAtup
    shrinkAT (SnocAtup t a) = shrinkAT t `SnocAtup` shrinkAcc a

    shrinkAF :: PreOpenAfun acc aenv' f -> PreOpenAfun acc aenv' f
    shrinkAF (Alam  f) = Alam (shrinkAF f)
    shrinkAF (Abody a) = Abody (shrinkAcc a)

    shrinkB :: PreBoundary acc aenv' t -> PreBoundary acc aenv' t
    shrinkB Clamp        = Clamp
    shrinkB Mirror       = Mirror
    shrinkB Wrap         = Wrap
    shrinkB (Constant c) = Constant c
    shrinkB (Function f) = Function (shrinkF f)


{--
-- A somewhat hacky example implementation of the reduction step. It requires a
-- function to open the recursive closure of an array term.
--
basicReduceAcc
    :: Kit acc
    => (forall aenv a. acc aenv a -> PreOpenAcc acc aenv a)
    -> UsesOfAcc acc
    -> ReduceAcc acc
basicReduceAcc unwrapAcc countAcc (unwrapAcc -> bnd) body@(unwrapAcc -> pbody)
  | Avar{} <- bnd                  = Stats.inline "Avar"  . Just $ rebuildA (subAtop bnd) pbody
  | allA (\_ n -> n <= lIMIT) uses = Stats.betaReduce msg . Just $ rebuildA (subAtop bnd) pbody
  | otherwise                      = Nothing
  where
    -- If the bound variable is used at most this many times, it will be inlined
    -- into the body. Since this implies an array computation could be inlined
    -- into a scalar expression, we limit the shrinking reduction for array
    -- computations to dead-code elimination only.
    --
    lIMIT = 0

    uses  = countAcc ZeroIdx body
    msg   = if allA (\_ n -> n <= lIMIT) uses
              then "dead acc"
              else "inline acc"       -- forced inlining when lIMIT > 1
--}

