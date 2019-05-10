{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE KindSignatures      #-}
{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE PatternGuards       #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell     #-}
{-# LANGUAGE TypeApplications    #-}
-- |
-- Module      : Data.Array.Accelerate.Trafo.Occurrence
-- Copyright   : [2016..2019] The Accelerate Team
-- License     : BSD3
--
-- Maintainer  : Trevor L. McDonell <trevor.mcdonell@gmail.com>
-- Stability   : experimental
-- Portability : non-portable (GHC extensions)
--
-- Count the number of occurrences of a variable in a term
--

module Data.Array.Accelerate.Trafo.Occurrence (

  -- Occurrence counting
  UsesOfAcc,
  UsesA, usesOfPreAcc, allA,
  UsesE, usesOfExp,    allE,

) where

-- standard library
import Data.Maybe                                                   ( fromJust )
import Data.Typeable                                                ( gcast )
import Prelude                                                      hiding ( all, exp, seq, init )

-- friends
import Data.Array.Accelerate.AST
import Data.Array.Accelerate.Analysis.Match
import Data.Array.Accelerate.Array.Sugar                            hiding ( Any )
import Data.Array.Accelerate.Error
import Data.Array.Accelerate.Product
import Data.Array.Accelerate.Trafo.Access
import Data.Array.Accelerate.Trafo.Base
import Data.Array.Accelerate.Type


-- Occurrence counting structure for scalar terms
--
data UsesE t where
  UsesE :: CountsE (EltRepr t) -> UsesE t

data CountsE t where
  CountsEunit   ::                           CountsE ()
  CountsEscalar :: {-# UNPACK #-} !Int    -> CountsE t
  CountsEpair   :: CountsE a -> CountsE b -> CountsE (a, b)

(+~) :: forall t. Elt t => UsesE t -> UsesE t -> UsesE t
UsesE a +~ UsesE b = UsesE (combineE (eltType @t) a b)

useE :: forall t e. (Elt t, Elt e) => TupleIdx (TupleRepr t) e -> UsesE t -> UsesE e -> UsesE t
useE tix (UsesE tup) (UsesE e) =
  case eltType @t of
    TypeRscalar (VectorScalarType v) -> UsesE (goV     v tup)
    t                                -> UsesE (goT tix t tup)
  where
    goT :: TupleIdx s e -> TupleType t' -> CountsE t' -> CountsE t'
    goT (SuccTupIdx ix) (TypeRpair t _) (CountsEpair a b) = CountsEpair (goT ix t a) b
    goT ZeroTupIdx      (TypeRpair _ t) (CountsEpair a b)
      | Just Refl <- matchTupleType t (eltType @e)
      = CountsEpair a (combineE t b e)
    goT _ _ _
      = $internalError "useE/goT" "inconsistent valuation"

    goV :: forall v a. VectorType (v a) -> CountsE (v a) -> CountsE (v a)
    goV v (CountsEscalar m)
      | Just Refl       <- matchTupleType (TypeRscalar (SingleScalarType a)) (eltType @e)
      , CountsEscalar n <- e
      = CountsEscalar (max m n) -- using different fields of a vector doesn't count
      where
        a :: SingleType a
        a = case v of
              VectorType _ t -> t
    goV _ _
      = $internalError "useE/goV" "inconsistent valuation"


combineE :: TupleType a -> CountsE a -> CountsE a -> CountsE a
combineE TypeRunit         CountsEunit         CountsEunit         = CountsEunit
combineE (TypeRpair t1 t2) (CountsEpair a1 a2) (CountsEpair b1 b2) = CountsEpair (combineE t1 a1 b1) (combineE t2 a2 b2)
combineE (TypeRscalar t)   (CountsEscalar a)   (CountsEscalar b)   =
  case t of
    VectorScalarType{} -> CountsEscalar (max a b) -- using different fields of a vector doesn't count
    SingleScalarType{} -> CountsEscalar (a + b)
combineE _ _ _
  = $internalError "combineE" "inconsistent valuation"


-- Check if a condition is true for every use count component
--
allE :: (Int -> Bool) -> UsesE t -> Bool
allE p (UsesE u) = go u
  where
    go :: CountsE t -> Bool
    go CountsEunit       = True
    go (CountsEscalar n) = p n
    go (CountsEpair a b) = go a && go b


-- Count the number of occurrences an in-scope scalar expression bound at the
-- given variable index recursively in a term.
--
usesOfExp :: forall acc env aenv s t. Elt s => Idx env s -> PreOpenExp acc env aenv t -> UsesE s
usesOfExp idx = countE
  where
    countE :: PreOpenExp acc env aenv e -> UsesE s
    countE = \case
      Let bnd body                    -> countE bnd +~ usesOfExp (SuccIdx idx) body
      Var v
        | Just Refl <- match idx v    -> one
        | otherwise                   -> zero
      Prj tix (Var v)
        | Just Refl <- match idx v    -> useE tix zero one
      Prj _ e                         -> countE e
      --
      Tuple t             -> countT t
      Const{}             -> zero
      Undef               -> zero
      IndexNil            -> zero
      IndexCons sl sz     -> countE sl +~ countE sz
      IndexHead sh        -> countE sh
      IndexTail sh        -> countE sh
      IndexSlice _ ix sh  -> countE ix +~ countE sh
      IndexFull _ ix sl   -> countE ix +~ countE sl
      IndexAny            -> zero
      ToIndex sh ix       -> countE sh +~ countE ix
      FromIndex sh i      -> countE sh +~ countE i
      Cond p t e          -> countE p  +~ countE t +~ countE e
      While p f x         -> countE x  +~ countF idx p +~ countF idx f
      PrimConst{}         -> zero
      PrimApp _ x         -> countE x
      Index _ sh          -> countE sh
      LinearIndex _ i     -> countE i
      Shape{}             -> zero
      ShapeSize sh        -> countE sh
      Intersect sh sz     -> countE sh +~ countE sz
      Union sh sz         -> countE sh +~ countE sz
      Foreign _ _ e       -> countE e

    countF :: Idx env' s -> PreOpenFun acc env' aenv f -> UsesE s
    countF idx' (Lam  f) = countF (SuccIdx idx') f
    countF idx' (Body b) = usesOfExp idx' b

    countT :: Tuple (PreOpenExp acc env aenv) e -> UsesE s
    countT NilTup        = zero
    countT (SnocTup t e) = countT t +~ countE e

    zero, one :: Elt e => UsesE e
    zero = init 0
    one  = init 1

    init :: forall e. Elt e => Int -> UsesE e
    init n = UsesE (go (eltType @e))
      where
        go :: TupleType e' -> CountsE e'
        go TypeRunit         = CountsEunit
        go TypeRscalar{}     = CountsEscalar n
        go (TypeRpair ta tb) = CountsEpair (go ta) (go tb)


-- Occurrence counting structure for array terms
--
data UsesA a where
  UsesA :: CountsA (ArrRepr a) -> UsesA a

data CountsA a where
  CountsAunit   :: CountsA ()
  CountsAarray  :: {-# UNPACK #-} !Int      -- shape accesses
                -> {-# UNPACK #-} !Int      -- payload accesses
                -> CountsA (Array sh e)
  CountsApair   :: CountsA a -> CountsA b -> CountsA (a, b)

(+^) :: forall a. Arrays a => UsesA a -> UsesA a -> UsesA a
UsesA a +^ UsesA b = UsesA (combineA (arrays @a) a b)

combineA :: ArraysR a -> CountsA a -> CountsA a -> CountsA a
combineA ArraysRunit            CountsAunit          CountsAunit         = CountsAunit
combineA ArraysRarray          (CountsAarray sa aa) (CountsAarray sb ab) = CountsAarray (sa+sb) (aa+ab)
combineA (ArraysRpair ae1 ae2) (CountsApair  a1 a2) (CountsApair  b1 b2) = CountsApair (combineA ae1 a1 b1) (combineA ae2 a2 b2)

useA :: forall t a. (Arrays t, Arrays a) => TupleIdx (TupleRepr t) a -> UsesA t -> UsesA a -> UsesA t
useA tix (UsesA tup) (UsesA a) = UsesA (go tix (arrays @t) tup)
  where
    go :: TupleIdx s a -> ArraysR t' -> CountsA t' -> CountsA t'
    go (SuccTupIdx ix) (ArraysRpair ae _) (CountsApair l r) = CountsApair (go ix ae l) r
    go ZeroTupIdx      (ArraysRpair _ ae) (CountsApair l r)
      | Just Refl <- matchArraysType ae (arrays @a)
      = CountsApair l (combineA ae r a)
    go _ _ _
      = $internalError "useA" "inconsistent valuation"

allA :: (Int -> Int -> Bool) -> UsesA a -> Bool
allA p (UsesA u) = go u
  where
    go :: CountsA a -> Bool
    go CountsAunit        = True
    go (CountsAarray s a) = p s a
    go (CountsApair a b)  = go a && go b

-- asAtuple :: forall arrs. (Arrays arrs, IsAtuple arrs) => UsesA arrs -> Atuple UsesA (TupleRepr arrs)
-- asAtuple UsesAarray{}   = $internalError "asAtuple" "inconsistent valuation"
-- asAtuple (UsesAtuple t) = t


-- Count the number of occurrences of the array term bound at the given
-- environment index.
--
type UsesOfAcc acc = forall aenv s t. Arrays s => Idx aenv s -> acc aenv t -> UsesA s

usesOfPreAcc
    :: forall acc aenv s t. (Kit acc, Arrays s)
    => UsesOfAcc acc
    -> Idx aenv s
    -> PreOpenAcc acc aenv t
    -> UsesA s
usesOfPreAcc countAcc idx = countP
  where
    countP :: PreOpenAcc acc aenv a -> UsesA s
    countP pacc =
      case pacc of
        Alet bnd body                   -> countA bnd +^ countAcc (SuccIdx idx) body
        Avar v
          | Just Refl <- match idx v    -> oneD
          | otherwise                   -> zero
        Aprj tix a
          | Just u          <- prjChain idx (inject pacc) oneD  -> u
          | Just (Atuple t) <- extract a                        -> countA (aprj tix t)
          | otherwise                                           -> countA a
        --
        Atuple t                -> countAT t
        Apply f a               -> countAF f idx +^ countA a
        Aforeign _ _ a          -> countA a
        Acond p t e             -> countE p  +^ countA t +^ countA e
        Awhile p f a            -> countAF p idx +^ countAF f idx +^ countA a
        Use{}                   -> zero
        Unit e                  -> countE e
        Reshape e a             -> countE e  +^ countA a
        Generate e f            -> countE e  +^ countF f
        Transform sh ix f a     -> countE sh +^ countF ix +^ countF f  +^ countA a
        Replicate _ sh a        -> countE sh +^ countA a
        Slice _ a sl            -> countE sl +^ countA a
        Map f a                 -> countF f  +^ countA a
        ZipWith f a1 a2         -> countF f  +^ countA a1 +^ countA a2
        Fold f z a              -> countF f  +^ countE z  +^ countA a
        Fold1 f a               -> countF f  +^ countA a
        FoldSeg f z a s         -> countF f  +^ countE z  +^ countA a  +^ countA s
        Fold1Seg f a s          -> countF f  +^ countA a  +^ countA s
        Scanl f z a             -> countF f  +^ countE z  +^ countA a
        Scanl' f z a            -> countF f  +^ countE z  +^ countA a
        Scanl1 f a              -> countF f  +^ countA a
        Scanr f z a             -> countF f  +^ countE z  +^ countA a
        Scanr' f z a            -> countF f  +^ countE z  +^ countA a
        Scanr1 f a              -> countF f  +^ countA a
        Permute f1 a1 f2 a2     -> countF f1 +^ countA a1 +^ countF f2 +^ countA a2
        Backpermute sh f a      -> countE sh +^ countF f  +^ countA a
        Stencil f b a           -> countF f  +^ countB b  +^ countA a
        Stencil2 f b1 a1 b2 a2  -> countF f  +^ countB b1 +^ countA a1 +^ countB b2 +^ countA a2

    countA :: acc aenv a -> UsesA s
    countA = countAcc idx

    countAT :: Atuple (acc aenv) a -> UsesA s
    countAT NilAtup        = zero
    countAT (SnocAtup t a) = countAT t +^ countA a

    countAF :: PreOpenAfun acc aenv' f -> Idx aenv' s -> UsesA s
    countAF (Alam  f) v = countAF f (SuccIdx v)
    countAF (Abody b) v = countAcc v b

    countB :: PreBoundary acc aenv a -> UsesA s
    countB Clamp        = zero
    countB Mirror       = zero
    countB Wrap         = zero
    countB Constant{}   = zero
    countB (Function f) = countF f

    countF :: PreOpenFun acc env aenv f -> UsesA s
    countF =
      case arrays @s of
        aeR@ArraysRarray | Just idx' <- castIdx aeR idx -> countF' . reduceAccessFun idx'
        _                                               -> countF'

    countE :: PreOpenExp acc env aenv e -> UsesA s
    countE =
      case arrays @s of
        aeR@ArraysRarray | Just idx' <- castIdx aeR idx -> countE' . reduceAccessExp idx'
        _                                               -> countE'

    castIdx :: ArraysR (Array sh e) -> Idx aenv s -> Maybe (Idx aenv (Array sh e))
    castIdx ArraysRarray = gcast -- TLM: ugh

    countF' :: PreOpenFun acc env aenv f -> UsesA s
    countF' (Lam  f) = countF' f
    countF' (Body b) = countE' b

    countE' :: PreOpenExp acc env aenv e -> UsesA s
    countE' exp =
      case exp of
        Index a sh
          | Just u <- prjChain idx a oneD -> u        +^ countE' sh
          | otherwise                     -> countA a +^ countE' sh
        LinearIndex a i
          | Just u <- prjChain idx a oneD -> u        +^ countE' i
          | otherwise                     -> countA a +^ countE' i
        Shape a
          | Just u <- prjChain idx a oneS -> u
          | otherwise                     -> countA a
        --
        Let bnd body            -> countE' bnd +^ countE' body
        Var{}                   -> zero
        Const{}                 -> zero
        Undef                   -> zero
        Tuple t                 -> countT' t
        Prj _ e                 -> countE' e
        IndexNil                -> zero
        IndexAny                -> zero
        IndexCons sl sz         -> countE' sl +^ countE' sz
        IndexHead sh            -> countE' sh
        IndexTail sh            -> countE' sh
        IndexSlice _ ix sh      -> countE' ix +^ countE' sh
        IndexFull _ ix sl       -> countE' ix +^ countE' sl
        ToIndex sh ix           -> countE' sh +^ countE' ix
        FromIndex sh i          -> countE' sh +^ countE' i
        Cond p t e              -> countE' p  +^ countE' t +^ countE' e
        While p f x             -> countF' p  +^ countF' f +^ countE' x
        PrimConst _             -> zero
        PrimApp _ x             -> countE' x
        ShapeSize sh            -> countE' sh
        Intersect sh sz         -> countE' sh +^ countE' sz
        Union sh sz             -> countE' sh +^ countE' sz
        Foreign _ _ e           -> countE' e

    countT' :: Tuple (PreOpenExp acc env aenv) e -> UsesA s
    countT' NilTup        = zero
    countT' (SnocTup t e) = countT' t +^ countE' e

    aprj :: TupleIdx t' a -> Atuple tup t' -> tup a
    aprj ZeroTupIdx       (SnocAtup _ a) = a
    aprj (SuccTupIdx tix) (SnocAtup t _) = aprj tix t

    prjChain :: Idx aenv s' -> acc aenv t' -> UsesA t' -> Maybe (UsesA s')
    prjChain ix a use =
      case fromJust (extract a) of  -- XXX merge artefact
        Avar v | Just Refl <- match ix v  -> Just use
        Aprj ix' a'                       -> prjChain ix a' (useA ix' zero use)
        _                                 -> Nothing

    zero, oneS, oneD :: forall a. Arrays a => UsesA a
    zero  = init 0 0
    oneS  = init 1 0  -- shape
    oneD  = init 0 1  -- data

    init :: forall a. Arrays a => Int -> Int -> UsesA a
    init n m = UsesA (go (arrays @a))
      where
        go :: ArraysR a' -> CountsA a'
        go ArraysRunit           = CountsAunit
        go ArraysRarray          = CountsAarray n m
        go (ArraysRpair ae1 ae2) = CountsApair (go ae1) (go ae2)

