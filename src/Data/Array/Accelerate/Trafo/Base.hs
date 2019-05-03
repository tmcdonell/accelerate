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

  -- Environments
  Gamma(..), incExp, prjExp, pushExp, lookupExp,
  Extend(..), append, bind,
  Sink(..), sink, sink1,
  Supplement(..), bindExps,

  subApply, inlineA,
  FreeProd, IsAtupleRepr,

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
import Data.Array.Accelerate.Array.Sugar                ( Array, Arrays(..), Shape, Elt, IsAtuple, ArrRepr, ArraysR(..), Tuple(..) )
import Data.Array.Accelerate.Error
import Data.Array.Accelerate.Product                    ( ProdRepr, IsProduct(..), ProdR(..) )
import Data.Array.Accelerate.Trafo.Dependency
import Data.Array.Accelerate.Trafo.Substitution

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

type DelayedOpenAfun      = PreOpenAfun DelayedOpenAcc
type DelayedOpenExp       = PreOpenExp DelayedOpenAcc
type DelayedOpenFun       = PreOpenFun DelayedOpenAcc
type DelayedOpenSeq       = PreOpenSeq (Int, Int) DelayedOpenAcc
type DelayedSeq           = StreamSeq (Int, Int) DelayedOpenAcc

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


-- Environments
-- ============

-- An environment that holds let-bound scalar expressions. The second
-- environment variable env' is used to project out the corresponding
-- index when looking up in the environment congruent expressions.
--
data Gamma acc env env' aenv where
  EmptyExp :: Gamma acc env env' aenv

  PushExp  :: Elt t
           => Gamma acc env env' aenv
           -> WeakPreOpenExp acc env aenv t
           -> Gamma acc env (env', t) aenv

data WeakPreOpenExp acc env aenv t where
  Subst    :: env :> env'
           -> PreOpenExp     acc env  aenv t
           -> PreOpenExp     acc env' aenv t {- LAZY -}
           -> WeakPreOpenExp acc env' aenv t

-- XXX: The simplifier calls this function every time it moves under a let
-- binding. This means we have a number of calls to 'weakenE' exponential in the
-- depth of nested let bindings, which quickly causes problems.
--
-- We can improve the situation slightly by observing that weakening by a single
-- variable does no less work than weaking by multiple variables at once; both
-- require a deep copy of the AST. By exploiting laziness (or, an IORef) we can
-- queue up multiple weakenings to happen in a single step.
--
-- <https://github.com/AccelerateHS/accelerate-llvm/issues/20>
--
incExp
    :: Kit acc
    => Gamma acc env     env' aenv
    -> Gamma acc (env,s) env' aenv
incExp EmptyExp        = EmptyExp
incExp (PushExp env w) = incExp env `PushExp` subs w
  where
    subs :: forall acc env aenv s t. Kit acc => WeakPreOpenExp acc env aenv t -> WeakPreOpenExp acc (env,s) aenv t
    subs (Subst k (e :: PreOpenExp acc env_ aenv t) _) = Subst k' e (weakenE k' e)
      where
        k' :: env_ :> (env,s)
        k' = SuccIdx . k

prjExp :: Idx env' t -> Gamma acc env env' aenv -> PreOpenExp acc env aenv t
prjExp ZeroIdx      (PushExp _   (Subst _ _ e)) = e
prjExp (SuccIdx ix) (PushExp env _)             = prjExp ix env
prjExp _            _                           = $internalError "prjExp" "inconsistent valuation"

pushExp :: Elt t => Gamma acc env env' aenv -> PreOpenExp acc env aenv t -> Gamma acc env (env',t) aenv
pushExp env e = env `PushExp` Subst id e e

-- XXX Merge artefact
lookupExp
    :: Kit acc
    => Gamma      acc env env' aenv
    -> PreOpenExp acc env      aenv t
    -> Maybe (Idx env' t)
lookupExp _ _ = Nothing
-- lookupExp EmptyExp        _ = Nothing
-- lookupExp (PushExp env e) x
--   | Just Refl <- match e x  = Just ZeroIdx
--   | otherwise               = SuccIdx `fmap` lookupExp env x

{--
weakenGamma1
    :: Kit acc
    => Gamma acc env env' aenv
    -> Gamma acc env env' (aenv,t)
weakenGamma1 EmptyExp        = EmptyExp
weakenGamma1 (PushExp env e) = PushExp (weakenGamma1 env) (weaken SuccIdx e)

sinkGamma
    :: Kit acc
    => Extend acc aenv aenv'
    -> Gamma acc env env' aenv
    -> Gamma acc env env' aenv'
sinkGamma _   EmptyExp        = EmptyExp
sinkGamma ext (PushExp env e) = PushExp (sinkGamma ext env) (sink ext e)
--}

-- As part of various transformations we often need to lift out array valued
-- inputs to be let-bound at a higher point.
--
-- The Extend type is a heterogeneous snoc-list of array terms that witnesses
-- how the array environment is extended by binding these additional terms.
--
data Extend acc aenv aenv' where
  BaseEnv :: Extend acc aenv aenv

  PushEnv :: Arrays a
          => Extend acc aenv aenv' -> acc aenv' a -> Extend acc aenv (aenv', a)

-- Append two environment witnesses
--
append :: Extend acc env env' -> Extend acc env' env'' -> Extend acc env env''
append x BaseEnv        = x
append x (PushEnv as a) = x `append` as `PushEnv` a

-- Bring into scope all of the array terms in the Extend environment list. This
-- converts a term in the inner environment (aenv') into the outer (aenv).
--
bind :: (Kit acc, Arrays a)
     => Extend acc aenv aenv'
     ->        acc      aenv' a
     ->        acc aenv       a
bind BaseEnv         = id
bind (PushEnv env a) = bind env . inject . Alet a

-- Sink a term from one array environment into another, where additional
-- bindings have come into scope according to the witness and no old things have
-- vanished.
--
sink :: Sink f => Extend acc env env' -> f env t -> f env' t
sink env = weaken (k env)
  where
    k :: Extend acc env env' -> Idx env t -> Idx env' t
    k BaseEnv       = Stats.substitution "sink" id
    k (PushEnv e _) = SuccIdx . k e

sink1 :: Sink f => Extend acc env env' -> f (env,s) t -> f (env',s) t
sink1 env = weaken (k env)
  where
    k :: Extend acc env env' -> Idx (env,s) t -> Idx (env',s) t
    k BaseEnv       = Stats.substitution "sink1" id
    k (PushEnv e _) = split . k e
    --
    split :: Idx (env,s) t -> Idx ((env,u),s) t
    split ZeroIdx      = ZeroIdx
    split (SuccIdx ix) = SuccIdx (SuccIdx ix)


-- This is the same as Extend, but for the scalar environment.
--
data Supplement acc env env' aenv where
  BaseSup :: Supplement acc env env aenv

  PushSup :: Elt e
          => Supplement acc env env'      aenv
          -> PreOpenExp acc     env'      aenv e
          -> Supplement acc env (env', e) aenv

bindExps :: (Kit acc, Elt e)
         => Supplement acc env env' aenv
         -> PreOpenExp acc env' aenv e
         -> PreOpenExp acc env  aenv e
bindExps BaseSup       = id
bindExps (PushSup g b) = bindExps g . Let b

-- Application via let binding.
--
subApply :: (RebuildableAcc acc, Arrays a)
         => PreOpenAfun acc aenv (a -> b)
         -> acc             aenv a
         -> PreOpenAcc  acc aenv b
subApply (Alam (Abody f)) a = Alet a f
subApply _                _ = error "subApply: inconsistent evaluation"

-- | Replace all occurrences of the first variable with the given array
-- expression. The environment shrinks.
--
inlineA :: Rebuildable f => f (aenv,s) t -> PreOpenAcc (AccClo f) aenv s -> f aenv t
inlineA f g = Stats.substitution "inlineA" $ rebuildA (subAtop g) f

-- Tuple manipulation
-- ==================

-- Note: [Tuple manipulation]
--
-- As a part of various transformations, we need to be able to transform tuples
-- and other product types. Unfortunately, due to the way product types are
-- represented in Accelerate, with a non injective relationship between surface
-- types and representation types, this causes problems. Supposing we have a
-- tuple like so
--
--   (a,b,c)
--
-- then suppose we want to pull b out of it, leaving us with (a,c). However,
-- the only way we can inspect the structure of a product is via its
-- representation type. That means we take
--
-- ((((),a),b),c)
--
-- and product (((),a),c). But what is the surface type corresponding to this
-- representation type?
--
-- FreeProd is a product type that gives a surface type for any product
-- representation type. That is, for all t, FreeProd (ProdRepr t) is a valid
-- product type. Additionally, for all t', ProdRepr (FreeProd t') ~ t'. This
-- gives us what we need in order to transform product types.
--

-- The free product. A surface product type for any given product representation
-- tyoe.
--
data FreeProd t where
  NilFreeProd  :: FreeProd ()
  SnocFreeProd :: Arrays s => FreeProd t -> s -> FreeProd (t,s)
  deriving ( Typeable )

instance IsProduct Arrays (FreeProd ()) where
  type ProdRepr (FreeProd ()) = ()
  fromProd _ = ()
  toProd   _ = NilFreeProd
  prod       = ProdRunit

instance (IsProduct Arrays (FreeProd t), Arrays s) => IsProduct Arrays (FreeProd (t,s)) where
  type ProdRepr (FreeProd (t,s)) = (ProdRepr (FreeProd t), s)
  fromProd (SnocFreeProd t s) = (fromProd @Arrays t, s)
  toProd (t,s)                = SnocFreeProd (toProd @Arrays t) s
  prod                        = ProdRsnoc (prod @Arrays @(FreeProd t))

instance (IsAtuple (FreeProd t), Typeable t, Arrays (FreeProd t), Arrays a) => Arrays (FreeProd (t,a)) where
  type ArrRepr (FreeProd (t,a)) = (ArrRepr (FreeProd t), ArrRepr a)
  arrays  = arrays @(FreeProd t) `ArraysRpair` arrays @a
  -- flavour = ArraysFtuple
  --
  toArr (t,a)                = SnocFreeProd (toArr t) (toArr a)
  fromArr (SnocFreeProd t a) = (fromArr t, fromArr a)

instance Arrays (FreeProd ()) where
  type ArrRepr (FreeProd ()) = ((),())
  arrays  = ArraysRpair ArraysRunit ArraysRunit
  -- flavour = ArraysFtuple
  --
  toArr   _ = NilFreeProd
  fromArr _ = ((),())

-- Unfortunately, the properties that hold for all array tuple
-- representations GHCs typechecker cannot infer.
--
type IsAtupleRepr t = (Arrays (FreeProd t), Typeable t, IsAtuple (FreeProd t), t ~ ProdRepr (FreeProd t))

