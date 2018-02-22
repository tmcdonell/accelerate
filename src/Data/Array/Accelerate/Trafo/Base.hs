{-# LANGUAGE CPP                  #-}
{-# LANGUAGE ConstraintKinds      #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE GADTs                #-}
{-# LANGUAGE PatternGuards        #-}
{-# LANGUAGE RankNTypes           #-}
{-# LANGUAGE RecordWildCards      #-}
{-# LANGUAGE ScopedTypeVariables  #-}
{-# LANGUAGE TemplateHaskell      #-}
{-# LANGUAGE TypeFamilies         #-}
{-# LANGUAGE TypeOperators        #-}
#if __GLASGOW_HASKELL__ <= 708
{-# LANGUAGE IncoherentInstances  #-}
{-# LANGUAGE OverlappingInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -fno-warn-unrecognised-pragmas #-}
#endif
-- |
-- Module      : Data.Array.Accelerate.Trafo.Base
-- Copyright   : [2012..2017] Manuel M T Chakravarty, Gabriele Keller, Trevor L. McDonell
-- License     : BSD3
--
-- Maintainer  : Trevor L. McDonell <tmcdonell@cse.unsw.edu.au>
-- Stability   : experimental
-- Portability : non-portable (GHC extensions)
--

module Data.Array.Accelerate.Trafo.Base (

  -- Toolkit
  Kit(..), Match(..), (:~:)(..),
  avarIn, kmap, fromOpenAfun,

  -- Delayed Arrays
  DelayedAcc,  DelayedOpenAcc(..),
  DelayedAfun, DelayedOpenAfun,
  DelayedExp,  DelayedOpenExp,
  DelayedFun,  DelayedOpenFun,
  matchDelayedOpenAcc, encodeDelayedOpenAcc, hashDelayedOpenAcc,

) where

-- standard library
import Control.Applicative
import Control.DeepSeq
import Crypto.Hash
import Data.ByteString.Builder
import Data.ByteString.Builder.Extra
import Data.Monoid
import Data.Type.Equality
import Text.PrettyPrint.ANSI.Leijen                     hiding ( (<$>), (<>) )
import Prelude                                          hiding ( until )

-- friends
import Data.Array.Accelerate.AST                        hiding ( Val(..) )
import Data.Array.Accelerate.Analysis.Hash
import Data.Array.Accelerate.Analysis.Match
import Data.Array.Accelerate.Array.Sugar                ( Array, Arrays, Shape, Elt )
import Data.Array.Accelerate.Pretty.Print
import Data.Array.Accelerate.Trafo.Substitution

import Data.Array.Accelerate.Debug.Stats                as Stats


-- Toolkit
-- =======

-- The bat utility belt of operations required to manipulate terms parameterised
-- by the recursive closure.
--
class (RebuildableAcc acc, Sink acc) => Kit acc where
  inject        :: PreOpenAcc acc aenv a -> acc aenv a
  extract       :: acc aenv a -> PreOpenAcc acc aenv a
  fromOpenAcc   :: OpenAcc aenv a -> acc aenv a
  --
  matchAcc      :: MatchAcc acc
  encodeAcc     :: EncodeAcc acc
  prettyAcc     :: PrettyAcc acc

instance Kit OpenAcc where
  inject                 = OpenAcc
  extract (OpenAcc pacc) = pacc
  fromOpenAcc            = id
  --
  {-# INLINEABLE encodeAcc #-}
  {-# INLINEABLE matchAcc  #-}
  {-# INLINEABLE prettyAcc #-}
  encodeAcc (OpenAcc pacc)                  = encodePreOpenAcc encodeAcc pacc
  matchAcc  (OpenAcc pacc1) (OpenAcc pacc2) = matchPreOpenAcc matchAcc encodeAcc pacc1 pacc2
  prettyAcc                                 = prettyOpenAcc

avarIn :: (Kit acc, Arrays arrs) => Idx aenv arrs -> acc aenv arrs
avarIn = inject  . Avar

kmap :: Kit acc => (PreOpenAcc acc aenv a -> PreOpenAcc acc aenv b) -> acc aenv a -> acc aenv b
kmap f = inject . f . extract

fromOpenAfun :: Kit acc => OpenAfun aenv f -> PreOpenAfun acc aenv f
fromOpenAfun (Abody a) = Abody $ fromOpenAcc a
fromOpenAfun (Alam f)  = Alam  $ fromOpenAfun f

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

-- data DelayedSeq t where
--   DelayedSeq :: Extend DelayedOpenAcc () aenv
--              -> DelayedOpenSeq aenv () t
--              -> DelayedSeq t

type DelayedOpenAfun    = PreOpenAfun DelayedOpenAcc
type DelayedOpenExp     = PreOpenExp DelayedOpenAcc
type DelayedOpenFun     = PreOpenFun DelayedOpenAcc
-- type DelayedOpenSeq     = PreOpenSeq DelayedOpenAcc

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
  inject                  = Manifest
  extract (Manifest pacc) = pacc
  extract Delayed{}       = error "DelayedAcc.extract"
  fromOpenAcc             = error "DelayedAcc.fromOpenAcc"
  --
  {-# INLINEABLE encodeAcc #-}
  {-# INLINEABLE matchAcc  #-}
  {-# INLINEABLE prettyAcc #-}
  encodeAcc               = encodeDelayedOpenAcc
  matchAcc                = matchDelayedOpenAcc
  prettyAcc               = prettyDelayedOpenAcc

instance NFData (DelayedOpenAfun aenv t) where
  rnf = rnfPreOpenAfun rnfDelayedOpenAcc

instance NFData (DelayedOpenAcc aenv t) where
  rnf = rnfDelayedOpenAcc

-- instance NFData (DelayedSeq t) where
--   rnf = rnfDelayedSeq


hashDelayedOpenAcc :: DelayedOpenAcc aenv a -> Hash
hashDelayedOpenAcc = hashlazy . toLazyByteString . encodeDelayedOpenAcc

{-# INLINEABLE encodeDelayedOpenAcc #-}
encodeDelayedOpenAcc :: EncodeAcc DelayedOpenAcc
encodeDelayedOpenAcc (Manifest pacc) = intHost $(hashQ "Manifest") <> encodePreOpenAcc encodeDelayedOpenAcc pacc
encodeDelayedOpenAcc Delayed{..}     = intHost $(hashQ "Delayed")  <> travE extentD <> travF indexD <> travF linearIndexD
  where
    {-# INLINE travE #-}
    travE :: DelayedExp aenv sh -> Builder
    travE = encodePreOpenExp encodeDelayedOpenAcc

    {-# INLINE travF #-}
    travF :: DelayedFun aenv f -> Builder
    travF = encodePreOpenFun encodeDelayedOpenAcc

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

rnfDelayedOpenAcc :: DelayedOpenAcc aenv t -> ()
rnfDelayedOpenAcc (Manifest pacc)    = rnfPreOpenAcc rnfDelayedOpenAcc pacc
rnfDelayedOpenAcc (Delayed sh ix lx) = rnfPreOpenExp rnfDelayedOpenAcc sh
                                 `seq` rnfPreOpenFun rnfDelayedOpenAcc ix
                                 `seq` rnfPreOpenFun rnfDelayedOpenAcc lx

{--
rnfDelayedSeq :: DelayedSeq t -> ()
rnfDelayedSeq (DelayedSeq env s) = rnfExtend rnfDelayedOpenAcc env
                             `seq` rnfPreOpenSeq rnfDelayedOpenAcc s

rnfExtend :: NFDataAcc acc -> Extend acc aenv aenv' -> ()
rnfExtend _    BaseEnv         = ()
rnfExtend rnfA (PushEnv env a) = rnfExtend rnfA env `seq` rnfA a
--}


-- Note: If we detect that the delayed array is simply accessing an array
-- variable, then just print the variable name. That is:
--
-- > let a0 = <...> in map f (Delayed (shape a0) (\x0 -> a0!x0))
--
-- becomes
--
-- > let a0 = <...> in map f a0
--
prettyDelayedOpenAcc :: PrettyAcc DelayedOpenAcc
prettyDelayedOpenAcc wrap aenv acc = case acc of
  Manifest pacc         -> prettyPreOpenAcc prettyDelayedOpenAcc wrap aenv pacc
  Delayed sh f _
    | Shape a           <- sh
    , Just Refl         <- match f (Lam (Body (Index a (Var ZeroIdx))))
    -> prettyDelayedOpenAcc wrap aenv a

    | otherwise
    -> wrap $ hang 2 (sep [ green (text "delayed")
                          , parens (align (prettyPreExp prettyDelayedOpenAcc (parens . align) aenv sh))
                          , parens (align (prettyPreFun prettyDelayedOpenAcc aenv f))
                          ])

{--
-- Pretty print delayed sequences
--
-- TLM: What is going on with this sequence thing, why is it closed?
--
prettyDelayedSeq
    :: (Doc -> Doc)                             -- apply to compound expressions
    -> DelayedSeq arrs
    -> Doc
prettyDelayedSeq wrap (DelayedSeq aenv s)
  | (d, lvl) <- pp env 0
  =  wrap $   (hang (text "let") 2 $ sep $ punctuate semi d)
          <+> (hang (text "in")  2 $ sep $ punctuate semi
                                         $ prettyPreSeq wrap prettyAcc lvl 0 s)
  where
    pp :: Extend DelayedOpenAcc aenv aenv' -> Int -> ([Doc], Int)
    pp BaseEnv          lvl = ([],lvl)
    pp (PushEnv env' a) lvl | (d', _) <- pp env' (lvl + 1)
                            = (prettyAcc lvl wrap a : d', lvl)
--}

