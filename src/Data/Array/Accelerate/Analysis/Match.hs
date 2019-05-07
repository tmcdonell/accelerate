{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE CPP                 #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE PatternGuards       #-}
{-# LANGUAGE PolyKinds           #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE TypeOperators       #-}
{-# OPTIONS_HADDOCK hide #-}
-- |
-- Module      : Data.Array.Accelerate.Analysis.Match
-- Copyright   : [2012..2019] The Accelerate Team
-- License     : BSD3
--
-- Maintainer  : Trevor L. McDonell <trevor.mcdonell@gmail.com>
-- Stability   : experimental
-- Portability : non-portable (GHC extensions)
--

module Data.Array.Accelerate.Analysis.Match (

  -- matching expressions
  MatchAcc,
  (:~:)(..),
  matchPreOpenAcc,
  matchPreOpenAfun,
  matchPreOpenExp,
  matchPreOpenFun,
  matchPrimFun,  matchPrimFun',
  -- matchOpenSeq,
  -- XXX merge artefact

  -- auxiliary
  matchIdx,
  matchTupleType, matchArraysType, matchArrayType, matchShapeType,
  matchIntegralType, matchFloatingType, matchNumType, matchScalarType,
  matchSource,

) where

-- standard library
import Control.Applicative                              ( liftA2 )
import Control.Monad                                    ( join )
import Data.Maybe
import Data.Typeable
import Unsafe.Coerce                                    ( unsafeCoerce )
import System.IO.Unsafe                                 ( unsafePerformIO )
import System.Mem.StableName
import Prelude                                          hiding ( exp )

#if __GLASGOW_HASKELL__ <= 708
import Control.Applicative                               ( (<$>), (<*>) )
#endif

-- friends
import Data.Array.Accelerate.Analysis.Hash
import Data.Array.Accelerate.Array.Representation       ( SliceIndex(..) )
import Data.Array.Accelerate.Array.Sugar
import Data.Array.Accelerate.AST
import Data.Array.Accelerate.Product
import Data.Array.Accelerate.Type


-- The type of matching array computations
--
type MatchAcc acc = forall aenv s t. acc aenv s -> acc aenv t -> Maybe (s :~: t)


-- XXX Merge artefact
-- {-# INLINEABLE matchOpenAcc #-}
-- matchOpenAcc
--     :: OpenAcc aenv s
--     -> OpenAcc aenv t
--     -> Maybe (s :~: t)
-- matchOpenAcc (OpenAcc acc1) (OpenAcc acc2) =
--   matchPreOpenAcc matchOpenAcc encodeOpenAcc acc1 acc2

-- Compute the congruence of two array computations. The nodes are congruent if
-- they have the same operator and their operands are congruent.
--
{-# INLINEABLE matchPreOpenAcc #-}
matchPreOpenAcc
    :: forall acc aenv s t.
       MatchAcc  acc
    -> EncodeAcc acc
    -> PreOpenAcc acc aenv s
    -> PreOpenAcc acc aenv t
    -> Maybe (s :~: t)
matchPreOpenAcc matchAcc encodeAcc = match
  where
    matchFun :: PreOpenFun acc env' aenv' u -> PreOpenFun acc env' aenv' v -> Maybe (u :~: v)
    matchFun = matchPreOpenFun matchAcc encodeAcc

    matchExp :: PreOpenExp acc env' aenv' u -> PreOpenExp acc env' aenv' v -> Maybe (u :~: v)
    matchExp = matchPreOpenExp matchAcc encodeAcc

    matchSeqIndex :: SeqIndex u -> SeqIndex v -> Maybe (u :~: v)
    matchSeqIndex SeqIndexRsingle SeqIndexRsingle = Just Refl
    matchSeqIndex SeqIndexRpair   SeqIndexRpair   = Just Refl
    matchSeqIndex _               _               = Nothing

    match :: PreOpenAcc acc aenv s -> PreOpenAcc acc aenv t -> Maybe (s :~: t)
    match (Alet x1 a1) (Alet x2 a2)
      | Just Refl <- matchAcc x1 x2
      , Just Refl <- matchAcc a1 a2
      = Just Refl

    match (Avar v1) (Avar v2)
      = matchIdx v1 v2

    match (Atuple t1) (Atuple t2)
      | Just Refl <- matchAtuple matchAcc t1 t2
      = gcast Refl  -- surface/representation type

    match (Aprj ix1 t1) (Aprj ix2 t2)
      | Just Refl <- matchAcc t1 t2
      , Just Refl <- matchTupleIdx ix1 ix2
      = Just Refl

    match (Apply f1 a1) (Apply f2 a2)
      | Just Refl <- matchPreOpenAfun matchAcc f1 f2
      , Just Refl <- matchAcc                  a1 a2
      = Just Refl

    match (Aforeign ff1 _ a1) (Aforeign ff2 _ a2)
      | Just Refl <- matchAcc a1 a2
      , unsafePerformIO $ do
          sn1 <- makeStableName ff1
          sn2 <- makeStableName ff2
          return $! hashStableName sn1 == hashStableName sn2
      = gcast Refl

    match (Acond p1 t1 e1) (Acond p2 t2 e2)
      | Just Refl <- matchExp p1 p2
      , Just Refl <- matchAcc t1 t2
      , Just Refl <- matchAcc e1 e2
      = Just Refl

    match (Awhile p1 f1 a1) (Awhile p2 f2 a2)
      | Just Refl <- matchAcc a1 a2
      , Just Refl <- matchPreOpenAfun matchAcc p1 p2
      , Just Refl <- matchPreOpenAfun matchAcc f1 f2
      = Just Refl

    match (Use a1) (Use a2)
      | Just Refl <- matchArrays (arrays @s) (arrays @t) a1 a2
      = gcast Refl

    match (Subarray ix1 sh1 a1) (Subarray ix2 sh2 a2)
      | Just Refl <- matchExp ix1 ix2
      , Just Refl <- matchExp sh1 sh2
      , Just Refl <- matchArrays ArraysRarray ArraysRarray a1 a2
      = gcast Refl

    match (Unit e1) (Unit e2)
      | Just Refl <- matchExp e1 e2
      = Just Refl

    match (Reshape sh1 a1) (Reshape sh2 a2)
      | Just Refl <- matchExp sh1 sh2
      , Just Refl <- matchAcc a1  a2
      = Just Refl

    match (Generate sh1 f1) (Generate sh2 f2)
      | Just Refl <- matchExp sh1 sh2
      , Just Refl <- matchFun f1  f2
      = Just Refl

    match (Transform sh1 ix1 f1 a1) (Transform sh2 ix2 f2 a2)
      | Just Refl <- matchExp sh1 sh2
      , Just Refl <- matchFun ix1 ix2
      , Just Refl <- matchFun f1  f2
      , Just Refl <- matchAcc a1  a2
      = Just Refl

    match (Replicate _ ix1 a1) (Replicate _ ix2 a2)
      | Just Refl <- matchExp ix1 ix2
      , Just Refl <- matchAcc a1  a2
      = gcast Refl  -- slice specification ??

    match (Slice _ a1 ix1) (Slice _ a2 ix2)
      | Just Refl <- matchAcc a1  a2
      , Just Refl <- matchExp ix1 ix2
      = gcast Refl  -- slice specification ??

    match (Map f1 a1) (Map f2 a2)
      | Just Refl <- matchFun f1 f2
      , Just Refl <- matchAcc a1 a2
      = Just Refl

    match (ZipWith f1 a1 b1) (ZipWith f2 a2 b2)
      | Just Refl <- matchFun f1 f2
      , Just Refl <- matchAcc a1 a2
      , Just Refl <- matchAcc b1 b2
      = Just Refl

    match (Fold f1 z1 a1) (Fold f2 z2 a2)
      | Just Refl <- matchFun f1 f2
      , Just Refl <- matchExp z1 z2
      , Just Refl <- matchAcc a1 a2
      = Just Refl

    match (Fold1 f1 a1) (Fold1 f2 a2)
      | Just Refl <- matchFun f1 f2
      , Just Refl <- matchAcc a1 a2
      = Just Refl

    match (FoldSeg f1 z1 a1 s1) (FoldSeg f2 z2 a2 s2)
      | Just Refl <- matchFun f1 f2
      , Just Refl <- matchExp z1 z2
      , Just Refl <- matchAcc a1 a2
      , Just Refl <- matchAcc s1 s2
      = Just Refl

    match (Fold1Seg f1 a1 s1) (Fold1Seg f2 a2 s2)
      | Just Refl <- matchFun f1 f2
      , Just Refl <- matchAcc a1 a2
      , Just Refl <- matchAcc s1 s2
      = Just Refl

    match (Scanl f1 z1 a1) (Scanl f2 z2 a2)
      | Just Refl <- matchFun f1 f2
      , Just Refl <- matchExp z1 z2
      , Just Refl <- matchAcc a1 a2
      = Just Refl

    match (Scanl' f1 z1 a1) (Scanl' f2 z2 a2)
      | Just Refl <- matchFun f1 f2
      , Just Refl <- matchExp z1 z2
      , Just Refl <- matchAcc a1 a2
      = Just Refl

    match (Scanl1 f1 a1) (Scanl1 f2 a2)
      | Just Refl <- matchFun f1 f2
      , Just Refl <- matchAcc a1 a2
      = Just Refl

    match (Scanr f1 z1 a1) (Scanr f2 z2 a2)
      | Just Refl <- matchFun f1 f2
      , Just Refl <- matchExp z1 z2
      , Just Refl <- matchAcc a1 a2
      = Just Refl

    match (Scanr' f1 z1 a1) (Scanr' f2 z2 a2)
      | Just Refl <- matchFun f1 f2
      , Just Refl <- matchExp z1 z2
      , Just Refl <- matchAcc a1 a2
      = Just Refl

    match (Scanr1 f1 a1) (Scanr1 f2 a2)
      | Just Refl <- matchFun f1 f2
      , Just Refl <- matchAcc a1 a2
      = Just Refl

    match (Permute f1 d1 p1 a1) (Permute f2 d2 p2 a2)
      | Just Refl <- matchFun f1 f2
      , Just Refl <- matchAcc d1 d2
      , Just Refl <- matchFun p1 p2
      , Just Refl <- matchAcc a1 a2
      = Just Refl

    match (Backpermute sh1 ix1 a1) (Backpermute sh2 ix2 a2)
      | Just Refl <- matchExp sh1 sh2
      , Just Refl <- matchFun ix1 ix2
      , Just Refl <- matchAcc a1  a2
      = Just Refl

    match (Stencil f1 b1 a1) (Stencil f2 b2 a2)
      | Just Refl <- matchFun f1 f2
      , Just Refl <- matchAcc a1 a2
      , matchBoundary matchAcc encodeAcc b1 b2
      = Just Refl

    match (Stencil2 f1 b1  a1  b2  a2) (Stencil2 f2 b1' a1' b2' a2')
      | Just Refl <- matchFun f1 f2
      , Just Refl <- matchAcc a1 a1'
      , Just Refl <- matchAcc a2 a2'
      , matchBoundary matchAcc encodeAcc b1 b1'
      , matchBoundary matchAcc encodeAcc b2 b2'
      = Just Refl

    match (Collect si1 min1 max1 i1 s1) (Collect si2 min2 max2 i2 s2)
      | Just Refl <- matchSeqIndex si1 si2
      , Just Refl <- matchExp min1 min2
      , Just Refl <- join $ liftA2 matchExp max1 max2
      , Just Refl <- join $ liftA2 matchExp i1 i2
      , Just Refl <- eqT3 s1 s2 -- index ~ index'
      , Just Refl <- matchSeq matchAcc encodeAcc s1 s2
      = Just Refl

    match _ _
      = Nothing


-- Array tuples
--
matchAtuple
    :: MatchAcc acc
    -> Atuple (acc aenv) s
    -> Atuple (acc aenv) t
    -> Maybe (s :~: t)
matchAtuple matchAcc (SnocAtup t1 a1) (SnocAtup t2 a2)
  | Just Refl <- matchAtuple matchAcc t1 t2
  , Just Refl <- matchAcc             a1 a2
  = Just Refl

matchAtuple _ NilAtup NilAtup = Just Refl
matchAtuple _ _       _       = Nothing


-- Array functions
--
{-# INLINEABLE matchPreOpenAfun #-}
matchPreOpenAfun
    :: MatchAcc acc
    -> PreOpenAfun acc aenv s
    -> PreOpenAfun acc aenv t
    -> Maybe (s :~: t)
matchPreOpenAfun m (Alam s) (Alam t)
  | Just Refl <- matchEnvTop        s t
  , Just Refl <- matchPreOpenAfun m s t
  = Just Refl
  where
    matchEnvTop :: (Arrays s, Arrays t)
                => PreOpenAfun acc (aenv, s) f -> PreOpenAfun acc (aenv, t) g -> Maybe (s :~: t)
    matchEnvTop _ _ = gcast Refl  -- ???

matchPreOpenAfun m (Abody s) (Abody t) = m s t
matchPreOpenAfun _ _         _         = Nothing


-- Match stencil boundaries
--
matchBoundary
    :: forall acc aenv sh t. Elt t
    => MatchAcc  acc
    -> EncodeAcc acc
    -> PreBoundary acc aenv (Array sh t)
    -> PreBoundary acc aenv (Array sh t)
    -> Bool
matchBoundary _ _ Clamp        Clamp        = True
matchBoundary _ _ Mirror       Mirror       = True
matchBoundary _ _ Wrap         Wrap         = True
matchBoundary _ _ (Constant s) (Constant t) = matchConst (eltType @t) s t
matchBoundary m h (Function f) (Function g)
  | Just Refl <- matchPreOpenFun m h f g
  = True
matchBoundary _ _ _ _
  = False


-- Match sequences
--
matchSeq
    :: forall idx acc aenv s t.
       MatchAcc  acc
    -> EncodeAcc acc
    -> PreOpenSeq idx acc aenv s
    -> PreOpenSeq idx acc aenv t
    -> Maybe (s :~: t)
matchSeq m h = match
  where
    matchExp :: PreOpenExp acc env' aenv' u -> PreOpenExp acc env' aenv' v -> Maybe (u :~: v)
    matchExp = matchPreOpenExp m h

    match :: forall aenv u v. PreOpenSeq idx acc aenv u -> PreOpenSeq idx acc aenv v -> Maybe (u :~: v)
    match (Producer p1 s1)   (Producer p2 s2)
      | Just Refl <- matchP p1 p2
      , Just Refl <- match s1 s2
      = Just Refl
    match (Consumer c1)   (Consumer c2)
      | Just Refl <- matchC c1 c2
      = Just Refl
    match (Reify _ ix1) (Reify _ ix2)
      | Just Refl <- m ix1 ix2
      = gcast Refl
    match _ _
      = Nothing

    matchP :: forall aenv u v. Producer idx acc aenv u -> Producer idx acc aenv v -> Maybe (u :~: v)
    matchP (Pull src1) (Pull src2)
      | Just Refl <- matchSource src1 src2
      = Just Refl
    matchP (Subarrays sh1 a1) (Subarrays sh2 a2)
      | Just Refl <- matchExp sh1 sh2
      , Just Refl <- matchArrays ArraysRarray ArraysRarray a1 a2
      = Just Refl
    matchP (FromSegs s1 n1 vs1) (FromSegs s2 n2 vs2)
      | Just Refl <- m s1 s2
      , Just Refl <- matchExp n1 n2
      , Just Refl <- m vs1 vs2
      = Just Refl
    matchP (Produce l1 f1) (Produce l2 f2)
      | Just Refl <- join $ liftA2 matchExp l1 l2
      , Just Refl <- matchPreOpenAfun m f1 f2
      = Just Refl
    -- matchP (MapBatch f1 c1 c1' a1 x1) (MapBatch f2 c2 c2' a2 x2)
    --   | Just Refl <- matchPreOpenAfun m f1 f2
    --   , Just Refl <- matchPreOpenAfun m c1 c2
    --   , Just Refl <- matchPreOpenAfun m c1' c2'
    --   , Just Refl <- m a1 a2
    --   , Just Refl <- m x1 x2
    --   = Just Refl
    matchP (ProduceAccum l1 f1 a1) (ProduceAccum l2 f2 a2)
      | Just Refl <- join $ liftA2 matchExp l1 l2
      , Just Refl <- matchPreOpenAfun m f1 f2
      , Just Refl <- m a1 a2
      = Just Refl
    matchP _ _
      = Nothing

    matchC :: forall aenv u v. Consumer idx acc aenv u -> Consumer idx acc aenv v -> Maybe (u :~: v)
    matchC (Last a1 d1) (Last a2 d2)
      | Just Refl <- m a1 a2
      , Just Refl <- m d1 d2
      = Just Refl
    matchC (FoldBatch f1 a1 x1) (FoldBatch f2 a2 x2)
      | Just Refl <- matchPreOpenAfun m f1 f2
      , Just Refl <- m a1 a2
      , Just Refl <- m x1 x2
      = Just Refl
    matchC (Stuple s1) (Stuple s2)
      | Just Refl <- matchAtuple (matchSeq m h) s1 s2
      = gcast Refl
    matchC _ _
      = Nothing

matchSource :: forall s t. Source s -> Source t -> Maybe (s :~: t)
matchSource (List arrs1) (List arrs2)
      | unsafePerformIO $ do
          sn1 <- makeStableName arrs1
          sn2 <- makeStableName arrs2
          return $! hashStableName sn1 == hashStableName sn2
      = gcast Refl
matchSource (RegularList _ arrs1) (RegularList _ arrs2)
      | unsafePerformIO $ do
          sn1 <- makeStableName arrs1
          sn2 <- makeStableName arrs2
          return $! hashStableName sn1 == hashStableName sn2
      = gcast Refl
-- XXX Merge artefact
-- matchSource (Function f1 a1) (Function f2 a2)
--       | unsafePerformIO $ do
--           sn1 <- makeStableName f1
--           sn2 <- makeStableName f2
--           return $! hashStableName sn1 == hashStableName sn2
--       , unsafePerformIO $ do
--           sn1 <- makeStableName a1
--           sn2 <- makeStableName a2
--           return $! hashStableName sn1 == hashStableName sn2
--       = gcast Refl
matchSource _ _ = Nothing


-- Match arrays
--
-- As a convenience, we are just comparing the stable names, but we could also
-- walk the structure comparing the underlying ptrsOfArrayData.
--
matchArrays :: ArraysR s -> ArraysR t -> s -> t -> Maybe (s :~: t)
matchArrays ArraysRunit ArraysRunit () ()
  = Just Refl

matchArrays (ArraysRpair a1 b1) (ArraysRpair a2 b2) (arr1,brr1) (arr2,brr2)
  | Just Refl <- matchArrays a1 a2 arr1 arr2
  , Just Refl <- matchArrays b1 b2 brr1 brr2
  = Just Refl

matchArrays ArraysRarray ArraysRarray (Array _ ad1) (Array _ ad2)
  | unsafePerformIO $ do
      sn1 <- makeStableName ad1
      sn2 <- makeStableName ad2
      return $! hashStableName sn1 == hashStableName sn2
  = gcast Refl

matchArrays _ _ _ _
  = Nothing


-- Compute the congruence of two scalar expressions. Two nodes are congruent if
-- either:
--
--  1. The nodes label constants and the contents are equal
--  2. They have the same operator and their operands are congruent
--
-- The below attempts to use real typed equality, but occasionally still needs
-- to use a cast, particularly when we can only match the representation types.
--
{-# INLINEABLE matchPreOpenExp #-}
matchPreOpenExp
    :: forall acc env aenv s t.
       MatchAcc  acc
    -> EncodeAcc acc
    -> PreOpenExp acc env aenv s
    -> PreOpenExp acc env aenv t
    -> Maybe (s :~: t)
matchPreOpenExp matchAcc encodeAcc = match
  where
    match :: forall env' aenv' s' t'.
             PreOpenExp acc env' aenv' s'
          -> PreOpenExp acc env' aenv' t'
          -> Maybe (s' :~: t')
    match (Let x1 e1) (Let x2 e2)
      | Just Refl <- match x1 x2
      , Just Refl <- match e1 e2
      = Just Refl

    match (Var v1) (Var v2)
      = matchIdx v1 v2

    match (Foreign ff1 _ e1) (Foreign ff2 _ e2)
      | Just Refl <- match e1 e2
      , unsafePerformIO $ do
          sn1 <- makeStableName ff1
          sn2 <- makeStableName ff2
          return $! hashStableName sn1 == hashStableName sn2
      = gcast Refl

    match (Const c1) (Const c2)
      | Just Refl <- matchTupleType (eltType @s') (eltType @t')
      , matchConst (eltType @s') c1 c2
      = gcast Refl  -- surface/representation type

    match Undef Undef
      | Just Refl <- matchTupleType (eltType @s') (eltType @t')
      = gcast Refl

    match (Coerce e1) (Coerce e2)
      | Just Refl <- matchTupleType (eltType @s') (eltType @t')
      , Just Refl <- match e1 e2
      = gcast Refl

    match (Tuple t1) (Tuple t2)
      | Just Refl <- matchTuple matchAcc encodeAcc t1 t2
      = gcast Refl  -- surface/representation type

    match (Prj ix1 t1) (Prj ix2 t2)
      | Just Refl <- match         t1  t2
      , Just Refl <- matchTupleIdx ix1 ix2
      = Just Refl

    match IndexAny IndexAny
      = gcast Refl  -- ???

    match IndexNil IndexNil
      = Just Refl

    match (IndexCons sl1 a1) (IndexCons sl2 a2)
      | Just Refl <- match sl1 sl2
      , Just Refl <- match a1 a2
      = Just Refl

    match (IndexHead sl1) (IndexHead sl2)
      | Just Refl <- match sl1 sl2
      = Just Refl

    match (IndexTail sl1) (IndexTail sl2)
      | Just Refl <- match sl1 sl2
      = Just Refl

    match (IndexTrans sl1) (IndexTrans sl2)
      | Just Refl <- match sl1 sl2
      = Just Refl

    match (IndexSlice sliceIndex1 _ sh1) (IndexSlice sliceIndex2 _ sh2)
      | Just Refl <- match sh1 sh2
      , Just Refl <- matchSliceRestrict sliceIndex1 sliceIndex2
      = gcast Refl  -- SliceIndex representation/surface type

    match (IndexFull sliceIndex1 ix1 sl1) (IndexFull sliceIndex2 ix2 sl2)
      | Just Refl <- match ix1 ix2
      , Just Refl <- match sl1 sl2
      , Just Refl <- matchSliceExtend sliceIndex1 sliceIndex2
      = gcast Refl  -- SliceIndex representation/surface type

    match (ToIndex sh1 i1) (ToIndex sh2 i2)
      | Just Refl <- match sh1 sh2
      , Just Refl <- match i1  i2
      = Just Refl

    match (FromIndex sh1 i1) (FromIndex sh2 i2)
      | Just Refl <- match i1  i2
      , Just Refl <- match sh1 sh2
      = Just Refl

    match (ToSlice _ sh1 i1) (ToSlice _ sh2 i2)
      | Just Refl <- match sh1 sh2
      , Just Refl <- match i1  i2
      = gcast Refl

    match (Cond p1 t1 e1) (Cond p2 t2 e2)
      | Just Refl <- match p1 p2
      , Just Refl <- match t1 t2
      , Just Refl <- match e1 e2
      = Just Refl

    match (While p1 f1 x1) (While p2 f2 x2)
      | Just Refl <- match x1 x2
      , Just Refl <- matchPreOpenFun matchAcc encodeAcc p1 p2
      , Just Refl <- matchPreOpenFun matchAcc encodeAcc f1 f2
      = Just Refl

    match (PrimConst c1) (PrimConst c2)
      = matchPrimConst c1 c2

    match (PrimApp f1 x1) (PrimApp f2 x2)
      | Just x1'  <- commutes encodeAcc f1 x1
      , Just x2'  <- commutes encodeAcc f2 x2
      , Just Refl <- match        x1' x2'
      , Just Refl <- matchPrimFun f1  f2
      = Just Refl

      | Just Refl <- match x1 x2
      , Just Refl <- matchPrimFun f1 f2
      = Just Refl

    match (Index a1 x1) (Index a2 x2)
      | Just Refl <- matchAcc a1 a2     -- should only be array indices
      , Just Refl <- match    x1 x2
      = Just Refl

    match (LinearIndex a1 x1) (LinearIndex a2 x2)
      | Just Refl <- matchAcc a1 a2
      , Just Refl <- match    x1 x2
      = Just Refl

    match (Shape a1) (Shape a2)
      | Just Refl <- matchAcc a1 a2     -- should only be array indices
      = Just Refl

    match (ShapeSize sh1) (ShapeSize sh2)
      | Just Refl <- match sh1 sh2
      = Just Refl

    match (Intersect sa1 sb1) (Intersect sa2 sb2)
      | Just Refl <- match sa1 sa2
      , Just Refl <- match sb1 sb2
      = Just Refl

    match (Union sa1 sb1) (Union sa2 sb2)
      | Just Refl <- match sa1 sa2
      , Just Refl <- match sb1 sb2
      = Just Refl

    match _ _
      = Nothing


-- Match scalar functions
--
{-# INLINEABLE matchPreOpenFun #-}
matchPreOpenFun
    :: MatchAcc  acc
    -> EncodeAcc acc
    -> PreOpenFun acc env aenv s
    -> PreOpenFun acc env aenv t
    -> Maybe (s :~: t)
matchPreOpenFun m h (Lam s) (Lam t)
  | Just Refl <- matchEnvTop         s t
  , Just Refl <- matchPreOpenFun m h s t
  = Just Refl
  where
    matchEnvTop :: (Elt s, Elt t) => PreOpenFun acc (env, s) aenv f -> PreOpenFun acc (env, t) aenv g -> Maybe (s :~: t)
    matchEnvTop _ _ = gcast Refl  -- ???

matchPreOpenFun m h (Body s) (Body t) = matchPreOpenExp m h s t
matchPreOpenFun _ _ _        _        = Nothing

-- Matching constants
--
matchConst :: TupleType a -> a -> a -> Bool
matchConst TypeRunit         ()      ()      = True
matchConst (TypeRscalar ty)  a       b       = evalEq ty (a,b)
matchConst (TypeRpair ta tb) (a1,b1) (a2,b2) = matchConst ta a1 a2 && matchConst tb b1 b2

evalEq :: ScalarType a -> (a, a) -> Bool
evalEq (SingleScalarType t) = evalEqSingle t
evalEq (VectorScalarType t) = evalEqVector t

evalEqSingle :: SingleType a -> (a, a) -> Bool
evalEqSingle (NumSingleType t)                                  = evalEqNum t
evalEqSingle (NonNumSingleType t) | NonNumDict <- nonNumDict t  = uncurry (==)

evalEqVector :: VectorType a -> (a, a) -> Bool
evalEqVector VectorType{} = uncurry (==)

evalEqNum :: NumType a -> (a, a) -> Bool
evalEqNum (IntegralNumType t) | IntegralDict <- integralDict t  = uncurry (==)
evalEqNum (FloatingNumType t) | FloatingDict <- floatingDict t  = uncurry (==)


-- Environment projection indices
--
{-# INLINEABLE matchIdx #-}
matchIdx :: Idx env s -> Idx env t -> Maybe (s :~: t)
matchIdx ZeroIdx     ZeroIdx     = Just Refl
matchIdx (SuccIdx u) (SuccIdx v) = matchIdx u v
matchIdx _           _           = Nothing


-- Tuple projection indices. Given the same tuple expression structure (tup),
-- check that the indices project identical elements.
--
{-# INLINEABLE matchTupleIdx #-}
matchTupleIdx :: TupleIdx tup s -> TupleIdx tup t -> Maybe (s :~: t)
matchTupleIdx ZeroTupIdx     ZeroTupIdx     = Just Refl
matchTupleIdx (SuccTupIdx s) (SuccTupIdx t) = matchTupleIdx s t
matchTupleIdx _              _              = Nothing

-- Tuples
--
matchTuple
    :: MatchAcc  acc
    -> EncodeAcc acc
    -> Tuple (PreOpenExp acc env aenv) s
    -> Tuple (PreOpenExp acc env aenv) t
    -> Maybe (s :~: t)
matchTuple _ _ NilTup          NilTup           = Just Refl
matchTuple m h (SnocTup t1 e1) (SnocTup t2 e2)
  | Just Refl <- matchTuple      m h t1 t2
  , Just Refl <- matchPreOpenExp m h e1 e2
  = Just Refl

matchTuple _ _ _               _                = Nothing


-- Slice specifications
--
matchSliceRestrict
    :: SliceIndex slix s co  sh
    -> SliceIndex slix' t co' sh
    -> Maybe (s :~: t)
matchSliceRestrict SliceNil SliceNil
  = Just Refl

matchSliceRestrict (SliceAll   sl1) (SliceAll   sl2)
  | Just Refl <- matchSliceRestrict sl1 sl2
  = Just Refl

matchSliceRestrict (SliceFixed sl1) (SliceFixed sl2)
  | Just Refl <- matchSliceRestrict sl1 sl2
  = Just Refl

matchSliceRestrict _ _
  = Nothing


matchSliceExtend
    :: SliceIndex slix sl co  s
    -> SliceIndex slix sl co' t
    -> Maybe (s :~: t)
matchSliceExtend SliceNil SliceNil
  = Just Refl

matchSliceExtend (SliceAll   sl1) (SliceAll   sl2)
  | Just Refl <- matchSliceExtend sl1 sl2
  = Just Refl

matchSliceExtend (SliceFixed sl1) (SliceFixed sl2)
  | Just Refl <- matchSliceExtend sl1 sl2
  = Just Refl

matchSliceExtend _ _
  = Nothing


-- Primitive constants and functions
--
matchPrimConst :: PrimConst s -> PrimConst t -> Maybe (s :~: t)
matchPrimConst (PrimMinBound s) (PrimMinBound t) = matchBoundedType s t
matchPrimConst (PrimMaxBound s) (PrimMaxBound t) = matchBoundedType s t
matchPrimConst (PrimPi s)       (PrimPi t)       = matchFloatingType s t
matchPrimConst _                _                = Nothing


-- Covariant function matching
--
{-# INLINEABLE matchPrimFun #-}
matchPrimFun :: PrimFun (a -> s) -> PrimFun (a -> t) -> Maybe (s :~: t)
matchPrimFun (PrimAdd _)                (PrimAdd _)                = Just Refl
matchPrimFun (PrimSub _)                (PrimSub _)                = Just Refl
matchPrimFun (PrimMul _)                (PrimMul _)                = Just Refl
matchPrimFun (PrimNeg _)                (PrimNeg _)                = Just Refl
matchPrimFun (PrimAbs _)                (PrimAbs _)                = Just Refl
matchPrimFun (PrimSig _)                (PrimSig _)                = Just Refl
matchPrimFun (PrimQuot _)               (PrimQuot _)               = Just Refl
matchPrimFun (PrimRem _)                (PrimRem _)                = Just Refl
matchPrimFun (PrimQuotRem _)            (PrimQuotRem _)            = Just Refl
matchPrimFun (PrimIDiv _)               (PrimIDiv _)               = Just Refl
matchPrimFun (PrimMod _)                (PrimMod _)                = Just Refl
matchPrimFun (PrimDivMod _)             (PrimDivMod _)             = Just Refl
matchPrimFun (PrimBAnd _)               (PrimBAnd _)               = Just Refl
matchPrimFun (PrimBOr _)                (PrimBOr _)                = Just Refl
matchPrimFun (PrimBXor _)               (PrimBXor _)               = Just Refl
matchPrimFun (PrimBNot _)               (PrimBNot _)               = Just Refl
matchPrimFun (PrimBShiftL _)            (PrimBShiftL _)            = Just Refl
matchPrimFun (PrimBShiftR _)            (PrimBShiftR _)            = Just Refl
matchPrimFun (PrimBRotateL _)           (PrimBRotateL _)           = Just Refl
matchPrimFun (PrimBRotateR _)           (PrimBRotateR _)           = Just Refl
matchPrimFun (PrimPopCount _)           (PrimPopCount _)           = Just Refl
matchPrimFun (PrimCountLeadingZeros _)  (PrimCountLeadingZeros _)  = Just Refl
matchPrimFun (PrimCountTrailingZeros _) (PrimCountTrailingZeros _) = Just Refl
matchPrimFun (PrimFDiv _)               (PrimFDiv _)               = Just Refl
matchPrimFun (PrimRecip _)              (PrimRecip _)              = Just Refl
matchPrimFun (PrimSin _)                (PrimSin _)                = Just Refl
matchPrimFun (PrimCos _)                (PrimCos _)                = Just Refl
matchPrimFun (PrimTan _)                (PrimTan _)                = Just Refl
matchPrimFun (PrimAsin _)               (PrimAsin _)               = Just Refl
matchPrimFun (PrimAcos _)               (PrimAcos _)               = Just Refl
matchPrimFun (PrimAtan _)               (PrimAtan _)               = Just Refl
matchPrimFun (PrimSinh _)               (PrimSinh _)               = Just Refl
matchPrimFun (PrimCosh _)               (PrimCosh _)               = Just Refl
matchPrimFun (PrimTanh _)               (PrimTanh _)               = Just Refl
matchPrimFun (PrimAsinh _)              (PrimAsinh _)              = Just Refl
matchPrimFun (PrimAcosh _)              (PrimAcosh _)              = Just Refl
matchPrimFun (PrimAtanh _)              (PrimAtanh _)              = Just Refl
matchPrimFun (PrimExpFloating _)        (PrimExpFloating _)        = Just Refl
matchPrimFun (PrimSqrt _)               (PrimSqrt _)               = Just Refl
matchPrimFun (PrimLog _)                (PrimLog _)                = Just Refl
matchPrimFun (PrimFPow _)               (PrimFPow _)               = Just Refl
matchPrimFun (PrimLogBase _)            (PrimLogBase _)            = Just Refl
matchPrimFun (PrimAtan2 _)              (PrimAtan2 _)              = Just Refl
matchPrimFun (PrimTruncate _ s)         (PrimTruncate _ t)         = matchIntegralType s t
matchPrimFun (PrimRound _ s)            (PrimRound _ t)            = matchIntegralType s t
matchPrimFun (PrimFloor _ s)            (PrimFloor _ t)            = matchIntegralType s t
matchPrimFun (PrimCeiling _ s)          (PrimCeiling _ t)          = matchIntegralType s t
matchPrimFun (PrimIsNaN _)              (PrimIsNaN _)              = Just Refl
matchPrimFun (PrimIsInfinite _)         (PrimIsInfinite _)         = Just Refl
matchPrimFun (PrimLt _)                 (PrimLt _)                 = Just Refl
matchPrimFun (PrimGt _)                 (PrimGt _)                 = Just Refl
matchPrimFun (PrimLtEq _)               (PrimLtEq _)               = Just Refl
matchPrimFun (PrimGtEq _)               (PrimGtEq _)               = Just Refl
matchPrimFun (PrimEq _)                 (PrimEq _)                 = Just Refl
matchPrimFun (PrimNEq _)                (PrimNEq _)                = Just Refl
matchPrimFun (PrimMax _)                (PrimMax _)                = Just Refl
matchPrimFun (PrimMin _)                (PrimMin _)                = Just Refl
matchPrimFun (PrimFromIntegral _ s)     (PrimFromIntegral _ t)     = matchNumType s t
matchPrimFun (PrimToFloating _ s)       (PrimToFloating _ t)       = matchFloatingType s t
matchPrimFun PrimLAnd                   PrimLAnd                   = Just Refl
matchPrimFun PrimLOr                    PrimLOr                    = Just Refl
matchPrimFun PrimLNot                   PrimLNot                   = Just Refl
matchPrimFun PrimOrd                    PrimOrd                    = Just Refl
matchPrimFun PrimChr                    PrimChr                    = Just Refl
matchPrimFun PrimBoolToInt              PrimBoolToInt              = Just Refl

matchPrimFun _ _
  = Nothing


-- Contravariant function matching
--
{-# INLINEABLE matchPrimFun' #-}
matchPrimFun' :: PrimFun (s -> a) -> PrimFun (t -> a) -> Maybe (s :~: t)
matchPrimFun' (PrimAdd _)                (PrimAdd _)                = Just Refl
matchPrimFun' (PrimSub _)                (PrimSub _)                = Just Refl
matchPrimFun' (PrimMul _)                (PrimMul _)                = Just Refl
matchPrimFun' (PrimNeg _)                (PrimNeg _)                = Just Refl
matchPrimFun' (PrimAbs _)                (PrimAbs _)                = Just Refl
matchPrimFun' (PrimSig _)                (PrimSig _)                = Just Refl
matchPrimFun' (PrimQuot _)               (PrimQuot _)               = Just Refl
matchPrimFun' (PrimRem _)                (PrimRem _)                = Just Refl
matchPrimFun' (PrimQuotRem _)            (PrimQuotRem _)            = Just Refl
matchPrimFun' (PrimIDiv _)               (PrimIDiv _)               = Just Refl
matchPrimFun' (PrimMod _)                (PrimMod _)                = Just Refl
matchPrimFun' (PrimDivMod _)             (PrimDivMod _)             = Just Refl
matchPrimFun' (PrimBAnd _)               (PrimBAnd _)               = Just Refl
matchPrimFun' (PrimBOr _)                (PrimBOr _)                = Just Refl
matchPrimFun' (PrimBXor _)               (PrimBXor _)               = Just Refl
matchPrimFun' (PrimBNot _)               (PrimBNot _)               = Just Refl
matchPrimFun' (PrimBShiftL _)            (PrimBShiftL _)            = Just Refl
matchPrimFun' (PrimBShiftR _)            (PrimBShiftR _)            = Just Refl
matchPrimFun' (PrimBRotateL _)           (PrimBRotateL _)           = Just Refl
matchPrimFun' (PrimBRotateR _)           (PrimBRotateR _)           = Just Refl
matchPrimFun' (PrimPopCount s)           (PrimPopCount t)           = matchIntegralType s t
matchPrimFun' (PrimCountLeadingZeros s)  (PrimCountLeadingZeros t)  = matchIntegralType s t
matchPrimFun' (PrimCountTrailingZeros s) (PrimCountTrailingZeros t) = matchIntegralType s t
matchPrimFun' (PrimFDiv _)               (PrimFDiv _)               = Just Refl
matchPrimFun' (PrimRecip _)              (PrimRecip _)              = Just Refl
matchPrimFun' (PrimSin _)                (PrimSin _)                = Just Refl
matchPrimFun' (PrimCos _)                (PrimCos _)                = Just Refl
matchPrimFun' (PrimTan _)                (PrimTan _)                = Just Refl
matchPrimFun' (PrimAsin _)               (PrimAsin _)               = Just Refl
matchPrimFun' (PrimAcos _)               (PrimAcos _)               = Just Refl
matchPrimFun' (PrimAtan _)               (PrimAtan _)               = Just Refl
matchPrimFun' (PrimSinh _)               (PrimSinh _)               = Just Refl
matchPrimFun' (PrimCosh _)               (PrimCosh _)               = Just Refl
matchPrimFun' (PrimTanh _)               (PrimTanh _)               = Just Refl
matchPrimFun' (PrimAsinh _)              (PrimAsinh _)              = Just Refl
matchPrimFun' (PrimAcosh _)              (PrimAcosh _)              = Just Refl
matchPrimFun' (PrimAtanh _)              (PrimAtanh _)              = Just Refl
matchPrimFun' (PrimExpFloating _)        (PrimExpFloating _)        = Just Refl
matchPrimFun' (PrimSqrt _)               (PrimSqrt _)               = Just Refl
matchPrimFun' (PrimLog _)                (PrimLog _)                = Just Refl
matchPrimFun' (PrimFPow _)               (PrimFPow _)               = Just Refl
matchPrimFun' (PrimLogBase _)            (PrimLogBase _)            = Just Refl
matchPrimFun' (PrimAtan2 _)              (PrimAtan2 _)              = Just Refl
matchPrimFun' (PrimTruncate s _)         (PrimTruncate t _)         = matchFloatingType s t
matchPrimFun' (PrimRound s _)            (PrimRound t _)            = matchFloatingType s t
matchPrimFun' (PrimFloor s _)            (PrimFloor t _)            = matchFloatingType s t
matchPrimFun' (PrimCeiling s _)          (PrimCeiling t _)          = matchFloatingType s t
matchPrimFun' (PrimIsNaN s)              (PrimIsNaN t)              = matchFloatingType s t
matchPrimFun' (PrimIsInfinite s)         (PrimIsInfinite t)         = matchFloatingType s t
matchPrimFun' (PrimMax _)                (PrimMax _)                = Just Refl
matchPrimFun' (PrimMin _)                (PrimMin _)                = Just Refl
matchPrimFun' (PrimFromIntegral s _)     (PrimFromIntegral t _)     = matchIntegralType s t
matchPrimFun' (PrimToFloating s _)       (PrimToFloating t _)       = matchNumType s t
matchPrimFun' PrimLAnd                   PrimLAnd                   = Just Refl
matchPrimFun' PrimLOr                    PrimLOr                    = Just Refl
matchPrimFun' PrimLNot                   PrimLNot                   = Just Refl
matchPrimFun' PrimOrd                    PrimOrd                    = Just Refl
matchPrimFun' PrimChr                    PrimChr                    = Just Refl
matchPrimFun' PrimBoolToInt              PrimBoolToInt              = Just Refl

matchPrimFun' (PrimLt s) (PrimLt t)
  | Just Refl <- matchSingleType s t
  = Just Refl

matchPrimFun' (PrimGt s) (PrimGt t)
  | Just Refl <- matchSingleType s t
  = Just Refl

matchPrimFun' (PrimLtEq s) (PrimLtEq t)
  | Just Refl <- matchSingleType s t
  = Just Refl

matchPrimFun' (PrimGtEq s) (PrimGtEq t)
  | Just Refl <- matchSingleType s t
  = Just Refl

matchPrimFun' (PrimEq s) (PrimEq t)
  | Just Refl <- matchSingleType s t
  = Just Refl

matchPrimFun' (PrimNEq s) (PrimNEq t)
  | Just Refl <- matchSingleType s t
  = Just Refl

matchPrimFun' _ _
  = Nothing

-- XXX merge artefact
-- matchOpenSeq :: PreOpenSeq idx OpenAcc aenv s -> PreOpenSeq idx OpenAcc aenv t -> Maybe (s :~: t)
-- matchOpenSeq = matchSeq matchOpenAcc hashOpenAcc

-- Match reified types
--
{-# INLINEABLE matchArraysType #-}
matchArraysType :: ArraysR s -> ArraysR t -> Maybe (s :~: t)
matchArraysType ArraysRunit         ArraysRunit         = Just Refl
matchArraysType (ArraysRpair s1 s2) (ArraysRpair t1 t2)
  | Just Refl <- matchArraysType s1 t1
  , Just Refl <- matchArraysType s2 t2
  = Just Refl

matchArraysType (ArraysRarray :: ArraysR s) (ArraysRarray :: ArraysR t)
  | Just Refl <- matchArrayType (undefined::s) (undefined::t)
  = Just Refl

matchArraysType _ _
  = Nothing


{-# INLINEABLE matchArrayType #-}
matchArrayType
    :: forall sh1 sh2 e1 e2. (Shape sh1, Shape sh2, Elt e1, Elt e2)
    => Array sh1 e1
    -> Array sh2 e2
    -> Maybe (Array sh1 e1 :~: Array sh2 e2)
matchArrayType _ _
  | Just Refl <- matchShapeType @sh1 @sh2
  , Just Refl <- matchTupleType (eltType @e1) (eltType @e2)
  = gcast Refl  -- surface/representation types

matchArrayType _ _
  = Nothing


{-# INLINEABLE matchTupleType #-}
matchTupleType :: TupleType s -> TupleType t -> Maybe (s :~: t)
matchTupleType TypeRunit         TypeRunit         = Just Refl
matchTupleType (TypeRscalar s)   (TypeRscalar t)   = matchScalarType s t
matchTupleType (TypeRpair s1 s2) (TypeRpair t1 t2)
  | Just Refl <- matchTupleType s1 t1
  , Just Refl <- matchTupleType s2 t2
  = Just Refl

matchTupleType _ _
  = Nothing


-- Match shapes (dimensionality)
--
-- XXX: Matching shapes is sort of a special case because the representation
-- types really are isomorphic to the surface type. However, 'gcast' does not
-- inline here, meaning that it will always do the fingerprint check, even if
-- the dimensions are known statically and thus the check could be elided as
-- a known branch.
--
{-# INLINEABLE matchShapeType #-}
matchShapeType :: forall s t. (Shape s, Shape t) => Maybe (s :~: t)
matchShapeType
  | Just Refl <- matchTupleType (eltType @s) (eltType @t)
#ifdef ACCELERATE_INTERNAL_CHECKS
  = gcast Refl
#else
  = Just (unsafeCoerce Refl)
#endif
  | otherwise
  = Nothing


-- Match reified type dictionaries
--
{-# INLINEABLE matchScalarType #-}
matchScalarType :: ScalarType s -> ScalarType t -> Maybe (s :~: t)
matchScalarType (SingleScalarType s) (SingleScalarType t) = matchSingleType s t
matchScalarType (VectorScalarType s) (VectorScalarType t) = matchVectorType s t
matchScalarType _                    _                    = Nothing

{-# INLINEABLE matchSingleType #-}
matchSingleType :: SingleType s -> SingleType t -> Maybe (s :~: t)
matchSingleType (NumSingleType s)    (NumSingleType t)    = matchNumType s t
matchSingleType (NonNumSingleType s) (NonNumSingleType t) = matchNonNumType s t
matchSingleType _                    _                    = Nothing

{-# INLINEABLE matchVectorType #-}
matchVectorType :: forall m n s t. VectorType (Vec n s) -> VectorType (Vec m t) -> Maybe (Vec n s :~: Vec m t)
matchVectorType (VectorType n s) (VectorType m t)
  | Just Refl <- if n == m
                   then Just (unsafeCoerce Refl :: n :~: m) -- XXX: we don't have an embedded KnownNat constraint, but
                   else Nothing                             -- this implementation is the same as 'GHC.TypeLits.sameNat'
  , Just Refl <- matchSingleType s t
  = Just Refl
matchVectorType _ _
  = Nothing

{-# INLINEABLE matchNumType #-}
matchNumType :: NumType s -> NumType t -> Maybe (s :~: t)
matchNumType (IntegralNumType s) (IntegralNumType t) = matchIntegralType s t
matchNumType (FloatingNumType s) (FloatingNumType t) = matchFloatingType s t
matchNumType _                   _                   = Nothing

{-# INLINEABLE matchBoundedType #-}
matchBoundedType :: BoundedType s -> BoundedType t -> Maybe (s :~: t)
matchBoundedType (IntegralBoundedType s) (IntegralBoundedType t) = matchIntegralType s t
matchBoundedType (NonNumBoundedType s)   (NonNumBoundedType t)   = matchNonNumType s t
matchBoundedType _                       _                       = Nothing

{-# INLINEABLE matchIntegralType #-}
matchIntegralType :: IntegralType s -> IntegralType t -> Maybe (s :~: t)
matchIntegralType TypeInt{}    TypeInt{}    = Just Refl
matchIntegralType TypeInt8{}   TypeInt8{}   = Just Refl
matchIntegralType TypeInt16{}  TypeInt16{}  = Just Refl
matchIntegralType TypeInt32{}  TypeInt32{}  = Just Refl
matchIntegralType TypeInt64{}  TypeInt64{}  = Just Refl
matchIntegralType TypeWord{}   TypeWord{}   = Just Refl
matchIntegralType TypeWord8{}  TypeWord8{}  = Just Refl
matchIntegralType TypeWord16{} TypeWord16{} = Just Refl
matchIntegralType TypeWord32{} TypeWord32{} = Just Refl
matchIntegralType TypeWord64{} TypeWord64{} = Just Refl
matchIntegralType _            _            = Nothing

{-# INLINEABLE matchFloatingType #-}
matchFloatingType :: FloatingType s -> FloatingType t -> Maybe (s :~: t)
matchFloatingType TypeHalf{}   TypeHalf{}   = Just Refl
matchFloatingType TypeFloat{}  TypeFloat{}  = Just Refl
matchFloatingType TypeDouble{} TypeDouble{} = Just Refl
matchFloatingType _            _            = Nothing

{-# INLINEABLE matchNonNumType #-}
matchNonNumType :: NonNumType s -> NonNumType t -> Maybe (s :~: t)
matchNonNumType TypeBool{} TypeBool{} = Just Refl
matchNonNumType TypeChar{} TypeChar{} = Just Refl
matchNonNumType _          _          = Nothing


-- Auxiliary
-- ---------

-- Discriminate binary functions that commute, and if so return the operands in
-- a stable ordering such that matching recognises expressions modulo
-- commutativity.
--
commutes
    :: forall acc env aenv a r.
       EncodeAcc acc
    -> PrimFun (a -> r)
    -> PreOpenExp acc env aenv a
    -> Maybe (PreOpenExp acc env aenv a)
commutes h f x = case f of
  PrimAdd{}     -> Just (swizzle x)
  PrimMul{}     -> Just (swizzle x)
  PrimBAnd{}    -> Just (swizzle x)
  PrimBOr{}     -> Just (swizzle x)
  PrimBXor{}    -> Just (swizzle x)
  PrimEq{}      -> Just (swizzle x)
  PrimNEq{}     -> Just (swizzle x)
  PrimMax{}     -> Just (swizzle x)
  PrimMin{}     -> Just (swizzle x)
  PrimLAnd      -> Just (swizzle x)
  PrimLOr       -> Just (swizzle x)
  _             -> Nothing
  where
    swizzle :: PreOpenExp acc env aenv (a',a') -> PreOpenExp acc env aenv (a',a')
    swizzle exp
      | Tuple (NilTup `SnocTup` a `SnocTup` b)  <- exp
      , hashPreOpenExp h a > hashPreOpenExp h b = Tuple (NilTup `SnocTup` b `SnocTup` a)
      --
      | otherwise                               = exp


-- | Equality over @k1 -> k2 -> k3 -> k4@
--
eqT3 :: forall t t' (a :: k1) (b :: k2) (c ::k3) (a' :: k1) (b' :: k2) (c' :: k3). (Typeable t, Typeable t')
     => t  a  b  c
     -> t' a' b' c'
     -> Maybe (t :~: t')
eqT3 _ _ = eqT :: Maybe (t :~: t')

