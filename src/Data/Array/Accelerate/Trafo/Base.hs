{-# LANGUAGE CPP                   #-}
{-# LANGUAGE ConstraintKinds       #-}
{-# LANGUAGE DeriveDataTypeable    #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE PatternGuards         #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE RecordWildCards       #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TemplateHaskell       #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE TypeOperators         #-}
#if __GLASGOW_HASKELL__ <= 708
{-# LANGUAGE IncoherentInstances   #-}
{-# LANGUAGE OverlappingInstances  #-}
{-# LANGUAGE UndecidableInstances  #-}
{-# OPTIONS_GHC -fno-warn-unrecognised-pragmas #-}
#endif
-- |
-- Module      : Data.Array.Accelerate.Trafo.Base
-- Copyright   : [2012..2019] The Accelerate Team
-- License     : BSD3
--
-- Maintainer  : Trevor L. McDonell <trevor.mcdonell@gmail.com>
-- Stability   : experimental
-- Portability : non-portable (GHC extensions)
--

module Data.Array.Accelerate.Trafo.Base (

  -- Toolkit
  Kit(..), Match(..), (:~:)(..),
  avarIn, kmap,

  -- XXX merge artefacts:
  fromOpenAfun, fromOpenExp, fromOpenFun,

  -- Delayed Arrays
  DelayedAcc,  DelayedOpenAcc(..),
  DelayedAfun, DelayedOpenAfun,
  DelayedSeq,  DelayedOpenSeq, StreamSeq(..),
  DelayedExp,  DelayedOpenExp,
  DelayedFun,  DelayedOpenFun,
  matchDelayedOpenAcc,
  encodeDelayedOpenAcc,

) where

-- standard library
import Control.DeepSeq
import Data.ByteString.Builder
import Data.ByteString.Builder.Extra
import Data.Maybe
import Data.Monoid
import Data.Typeable
import Prelude                                          hiding ( until )

#if __GLASGOW_HASKELL__ <= 708
import Control.Applicative                              ( (<$>), (<*>) )
#endif

-- friends
import Data.Array.Accelerate.AST                        hiding ( Val(..) )
import Data.Array.Accelerate.Analysis.Hash
import Data.Array.Accelerate.Analysis.Match
import Data.Array.Accelerate.Array.Sugar                ( Array, Arrays(..), Shape, Elt, Tuple(..) )
import Data.Array.Accelerate.Trafo.Dependency
import Data.Array.Accelerate.Trafo.Substitution
import {-# SOURCE #-} Data.Array.Accelerate.Trafo.Environment -- XXX merge artefact

import Data.Array.Accelerate.Debug.Stats                as Stats


-- Toolkit
-- =======

-- The bat utility belt of operations required to manipulate terms parameterised
-- by the recursive closure.
--
class (RebuildableAcc acc, Sink acc) => Kit acc where
  inject          :: PreOpenAcc acc aenv a -> acc aenv a
  extract         :: acc aenv a -> Maybe (PreOpenAcc acc aenv a)
  --
  matchAcc        :: MatchAcc acc
  encodeAcc       :: EncodeAcc acc
  dependenciesAcc :: DependenciesAcc acc

  -- XXX Merge artefacts
  -- This only had a single non-bottom implementation, for the OpenAcc
  -- instance---this needs to be replaced with something sensible
  -- fromOpenAcc   :: OpenAcc aenv a -> acc aenv a

instance Kit OpenAcc where
  {-# INLINEABLE encodeAcc       #-}
  {-# INLINEABLE matchAcc        #-}
  {-# INLINEABLE dependenciesAcc #-}
  inject                 = OpenAcc
  extract (OpenAcc pacc) = Just pacc
  encodeAcc              = encodeOpenAcc
  matchAcc               = matchOpenAcc
  dependenciesAcc        = dependenciesOpenAcc

encodeOpenAcc :: EncodeAcc OpenAcc
encodeOpenAcc options (OpenAcc pacc) = encodePreOpenAcc options encodeAcc pacc

matchOpenAcc :: MatchAcc OpenAcc
matchOpenAcc (OpenAcc pacc1) (OpenAcc pacc2) = matchPreOpenAcc matchAcc encodeAcc pacc1 pacc2

avarIn :: (Kit acc, Arrays arrs) => Idx aenv arrs -> acc aenv arrs
avarIn = inject  . Avar

kmap :: Kit acc => (PreOpenAcc acc aenv a -> PreOpenAcc acc aenv' a') -> acc aenv a -> acc aenv' a'
kmap f = inject . f . fromJust . extract

fromOpenAcc :: Kit acc => OpenAcc aenv a -> acc aenv a
fromOpenAcc (OpenAcc pacc) = error "fromOpenAcc" -- XXX merge artefact

fromOpenAfun :: Kit acc => OpenAfun aenv f -> PreOpenAfun acc aenv f
fromOpenAfun (Abody a) = Abody $ fromOpenAcc a
fromOpenAfun (Alam f)  = Alam  $ fromOpenAfun f

fromOpenExp :: Kit acc => OpenExp env aenv e -> PreOpenExp acc env aenv e
fromOpenExp = cvtE
  where
    cvtA :: Kit acc => OpenAcc aenv t -> acc aenv t
    cvtA = fromOpenAcc -- XXX Merge artefact

    cvtT :: Kit acc => Tuple (OpenExp env aenv) t -> Tuple (PreOpenExp acc env aenv) t
    cvtT tup = case tup of
      NilTup      -> NilTup
      SnocTup t a -> cvtT t `SnocTup` cvtE a

    cvtF :: Kit acc => OpenFun env aenv t -> PreOpenFun acc env aenv t
    cvtF = fromOpenFun

    cvtE :: Kit acc => OpenExp env aenv t -> PreOpenExp acc env aenv t
    cvtE exp =
      case exp of
        Let bnd body            -> Let (cvtE bnd) (cvtE body)
        Var ix                  -> Var ix
        Const c                 -> Const c
        Tuple tup               -> Tuple (cvtT tup)
        Prj tup t               -> Prj tup (cvtE t)
        IndexNil                -> IndexNil
        IndexCons sh sz         -> IndexCons (cvtE sh) (cvtE sz)
        IndexHead sh            -> IndexHead (cvtE sh)
        IndexTail sh            -> IndexTail (cvtE sh)
        IndexTrans sh           -> IndexTrans (cvtE sh)
        IndexAny                -> IndexAny
        IndexSlice x ix sh      -> IndexSlice x (cvtE ix) (cvtE sh)
        IndexFull x ix sl       -> IndexFull x (cvtE ix) (cvtE sl)
        ToIndex sh ix           -> ToIndex (cvtE sh) (cvtE ix)
        FromIndex sh ix         -> FromIndex (cvtE sh) (cvtE ix)
        ToSlice x sh i          -> ToSlice x (cvtE sh) (cvtE i)
        Cond p t e              -> Cond (cvtE p) (cvtE t) (cvtE e)
        While p f x             -> While (cvtF p) (cvtF f) (cvtE x)
        PrimConst c             -> PrimConst c
        PrimApp f x             -> PrimApp f (cvtE x)
        Index a sh              -> Index (cvtA a) (cvtE sh)
        LinearIndex a i         -> LinearIndex (cvtA a) (cvtE i)
        Shape a                 -> Shape (cvtA a)
        ShapeSize sh            -> ShapeSize (cvtE sh)
        Intersect s t           -> Intersect (cvtE s) (cvtE t)
        Union s t               -> Union (cvtE s) (cvtE t)
        Foreign ff f e          -> Foreign ff (cvtF f) (cvtE e)

fromOpenFun :: Kit acc
            => OpenFun env aenv t
            -> PreOpenFun acc env aenv t
fromOpenFun fun =
  case fun of
    Body b -> Body (fromOpenExp b)
    Lam f  -> Lam (fromOpenFun f)

-- A class for testing the equality of terms homogeneously, returning a witness
-- to the existentially quantified terms in the positive case.
--
class Match f where
  match :: f s -> f t -> Maybe (s :~: t)

instance Match (Idx env) where
  {-# INLINEABLE match #-}
  match = matchIdx

instance Kit acc => Match (PreOpenExp acc env aenv) where
  {-# INLINEABLE match #-}
  match = matchPreOpenExp matchAcc encodeAcc

instance Kit acc => Match (PreOpenFun acc env aenv) where
  {-# INLINEABLE match #-}
  match = matchPreOpenFun matchAcc encodeAcc

instance Kit acc => Match (PreOpenAcc acc aenv) where
  {-# INLINEABLE match #-}
  match = matchPreOpenAcc matchAcc encodeAcc

instance {-# INCOHERENT #-} Kit acc => Match (acc aenv) where
  {-# INLINEABLE match #-}
  match = matchAcc


-- Delayed Arrays
-- ==============

-- The type of delayed arrays. This representation is used to annotate the AST
-- in the recursive knot to distinguish standard AST terms from operand arrays
-- that should be embedded into their consumers.
--
type DelayedAcc         = DelayedOpenAcc ()
type DelayedAfun        = PreOpenAfun DelayedOpenAcc ()

type DelayedExp         = DelayedOpenExp ()
type DelayedFun         = DelayedOpenFun ()

data StreamSeq index acc t where
  StreamSeq :: Extend acc () aenv -> PreOpenSeq index acc aenv t -> StreamSeq index acc t

type DelayedOpenAfun    = PreOpenAfun DelayedOpenAcc
type DelayedOpenExp     = PreOpenExp DelayedOpenAcc
type DelayedOpenFun     = PreOpenFun DelayedOpenAcc
type DelayedOpenSeq     = PreOpenSeq (Int, Int) DelayedOpenAcc
type DelayedSeq         = StreamSeq (Int, Int) DelayedOpenAcc

data DelayedOpenAcc aenv a where
  Manifest              :: PreOpenAcc DelayedOpenAcc aenv a -> DelayedOpenAcc aenv a

  Delayed               :: (Shape sh, Elt e) =>
    { extentD           :: PreExp DelayedOpenAcc aenv sh
    , indexD            :: PreFun DelayedOpenAcc aenv (sh  -> e)
    , linearIndexD      :: PreFun DelayedOpenAcc aenv (Int -> e)
    }                   -> DelayedOpenAcc aenv (Array sh e)

instance Rebuildable DelayedOpenAcc where
  type AccClo DelayedOpenAcc = DelayedOpenAcc
  {-# INLINEABLE rebuildPartial #-}
  rebuildPartial v acc = case acc of
    Manifest pacc -> Manifest <$> rebuildPartial v pacc
    Delayed{..}   -> Delayed  <$> rebuildPartial v extentD
                              <*> rebuildPartial v indexD
                              <*> rebuildPartial v linearIndexD

instance Sink DelayedOpenAcc where
  weaken k = Stats.substitution "weaken" . rebuildA (Avar . k)

instance Kit DelayedOpenAcc where
  {-# INLINEABLE encodeAcc       #-}
  {-# INLINEABLE matchAcc        #-}
  {-# INLINEABLE dependenciesAcc #-}
  inject                  = Manifest
  extract (Manifest pacc) = Just pacc
  extract Delayed{}       = Nothing
  encodeAcc               = encodeDelayedOpenAcc
  matchAcc                = matchDelayedOpenAcc
  dependenciesAcc         = dependenciesDelayed

instance NFData (DelayedOpenAfun aenv t) where
  rnf = rnfPreOpenAfun rnfDelayedOpenAcc

instance NFData (DelayedOpenAcc aenv t) where
  rnf = rnfDelayedOpenAcc

instance NFData (StreamSeq index OpenAcc t) where
  rnf = rnfStreamSeq rnfOpenAcc

instance NFData (DelayedSeq t) where
  rnf = rnfStreamSeq rnfDelayedOpenAcc

{-# INLINEABLE encodeDelayedOpenAcc #-}
encodeDelayedOpenAcc :: EncodeAcc DelayedOpenAcc
encodeDelayedOpenAcc options acc =
  let
      travE :: DelayedExp aenv sh -> Builder
      travE = encodePreOpenExp options encodeDelayedOpenAcc

      travF :: DelayedFun aenv f -> Builder
      travF = encodePreOpenFun options encodeDelayedOpenAcc

      travA :: PreOpenAcc DelayedOpenAcc aenv a -> Builder
      travA = encodePreOpenAcc options encodeDelayedOpenAcc

      deep :: Builder -> Builder
      deep x | perfect options = x
             | otherwise       = mempty
  in
  case acc of
    Manifest pacc   -> intHost $(hashQ ("Manifest" :: String)) <> deep (travA pacc)
    Delayed sh f g  -> intHost $(hashQ ("Delayed"  :: String)) <> travE sh <> travF f <> travF g

{-# INLINEABLE matchDelayedOpenAcc #-}
matchDelayedOpenAcc :: MatchAcc DelayedOpenAcc
matchDelayedOpenAcc (Manifest pacc1) (Manifest pacc2)
  = matchPreOpenAcc matchDelayedOpenAcc encodeDelayedOpenAcc pacc1 pacc2

matchDelayedOpenAcc (Delayed sh1 ix1 lx1) (Delayed sh2 ix2 lx2)
  | Just Refl <- matchPreOpenExp matchDelayedOpenAcc encodeDelayedOpenAcc sh1 sh2
  , Just Refl <- matchPreOpenFun matchDelayedOpenAcc encodeDelayedOpenAcc ix1 ix2
  , Just Refl <- matchPreOpenFun matchDelayedOpenAcc encodeDelayedOpenAcc lx1 lx2
  = Just Refl

matchDelayedOpenAcc _ _
  = Nothing

{-# INLINEABLE dependenciesDelayed #-}
dependenciesDelayed :: DependenciesAcc DelayedOpenAcc
dependenciesDelayed acc = case acc of
  Manifest pacc  -> dependenciesPreAcc dependenciesDelayed pacc
  Delayed sh f _ -> dependenciesExp dependenciesDelayed sh <> dependenciesFun dependenciesDelayed f


rnfDelayedOpenAcc :: DelayedOpenAcc aenv t -> ()
rnfDelayedOpenAcc (Manifest pacc)    = rnfPreOpenAcc rnfDelayedOpenAcc pacc
rnfDelayedOpenAcc (Delayed sh ix lx) = rnfPreOpenExp rnfDelayedOpenAcc sh
                                 `seq` rnfPreOpenFun rnfDelayedOpenAcc ix
                                 `seq` rnfPreOpenFun rnfDelayedOpenAcc lx

rnfStreamSeq :: NFDataAcc acc -> StreamSeq index acc t -> ()
rnfStreamSeq rnfA (StreamSeq env s) = rnfExtend rnfA env
                                `seq` rnfPreOpenSeq rnfA s

rnfExtend :: NFDataAcc acc -> Extend acc aenv aenv' -> ()
rnfExtend _    BaseEnv         = ()
rnfExtend rnfA (PushEnv env a) = rnfExtend rnfA env `seq` rnfA a

