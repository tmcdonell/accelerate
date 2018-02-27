{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE KindSignatures      #-}
{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE PatternGuards       #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell     #-}
-- |
-- Module      : Data.Array.Accelerate.Trafo.Occurrence
-- Copyright   : [2016..2018] Robert Clifton-Everest, Trevor L. McDonell
-- License     : BSD3
--
-- Maintainer  : Trevor L. McDonell <tmcdonell@cse.unsw.edu.au>
-- Stability   : experimental
-- Portability : non-portable (GHC extensions)
--
-- Count the number of occurrences of a variable in a term
--

module Data.Array.Accelerate.Trafo.Occurrence (

  -- Occurrence counting
  UsesOfAcc,
  UsesA, usesOfPreAcc, allA, asAtuple,
  UsesE, usesOfExp,    allE,

) where

-- standard library
import Data.Proxy
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
UsesE a +~ UsesE b = UsesE (combineE (eltType (undefined::t)) a b)

useE :: forall t e. (Elt t, Elt e) => TupleIdx (TupleRepr t) e -> UsesE t -> UsesE e -> UsesE t
useE tix (UsesE tup) (UsesE e) =
  case eltType (undefined::t) of
    TypeRscalar (VectorScalarType v) -> UsesE (goV     v tup)
    t                                -> UsesE (goT tix t tup)
  where
    goT :: TupleIdx s e -> TupleType t' -> CountsE t' -> CountsE t'
    goT (SuccTupIdx ix) (TypeRpair t _) (CountsEpair a b) = CountsEpair (goT ix t a) b
    goT ZeroTupIdx      (TypeRpair _ t) (CountsEpair a b)
      | Just Refl <- matchTupleType t (eltType (undefined::e))
      = CountsEpair a (combineE t b e)
    goT _ _ _
      = $internalError "useE/goT" "inconsistent valuation"

    goV :: forall v a. VectorType (v a) -> CountsE (v a) -> CountsE (v a)
    goV v (CountsEscalar m)
      | Just Refl       <- matchTupleType (TypeRscalar (SingleScalarType a)) (eltType (undefined::e))
      , CountsEscalar n <- e
      = CountsEscalar (max m n) -- using different fields of a vector doesn't count
      where
        a :: SingleType a
        a = case v of
              Vector2Type  t -> t
              Vector3Type  t -> t
              Vector4Type  t -> t
              Vector8Type  t -> t
              Vector16Type t -> t
    goV _ _
      = $internalError "useE/goV" "inconsistent valuation"


combineE :: TupleType a -> CountsE a -> CountsE a -> CountsE a
combineE TypeRunit         CountsEunit         CountsEunit         = CountsEunit
combineE (TypeRpair ta tb) (CountsEpair a1 b1) (CountsEpair a2 b2) = CountsEpair (combineE ta a1 a2) (combineE tb b1 b2)
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
    init n = UsesE (go (eltType (undefined::e)))
      where
        go :: TupleType e' -> CountsE e'
        go TypeRunit         = CountsEunit
        go TypeRscalar{}     = CountsEscalar n
        go (TypeRpair ta tb) = CountsEpair (go ta) (go tb)


-- Occurrence counting structure for array terms
--
data UsesA a where
  UsesAarray  :: {-# UNPACK #-} !Int      -- shape accesses
              -> {-# UNPACK #-} !Int      -- payload accesses
              -> UsesA (Array sh e)
  UsesAtuple  :: Atuple UsesA (TupleRepr arrs) -> UsesA arrs

(+^) :: UsesA a -> UsesA a -> UsesA a
UsesAarray s1 d1 +^ UsesAarray s2 d2 = UsesAarray (s1+s2) (d1+d2)
UsesAtuple tup1  +^ UsesAtuple tup2  = UsesAtuple (go tup1 tup2)
  where
    go :: Atuple UsesA t -> Atuple UsesA t -> Atuple UsesA t
    go NilAtup          NilAtup          = NilAtup
    go (SnocAtup t1 a1) (SnocAtup t2 a2) = go t1 t2 `SnocAtup` (a1 +^ a2)
(+^) _ _ = $internalError "(+^)" "inconsistent valuation"

useA :: forall t a. (Arrays t, IsAtuple t) => TupleIdx (TupleRepr t) a -> UsesA t -> UsesA a -> UsesA t
useA _   UsesAarray{}     _ = $internalError "useA" "inconsistent valuation"
useA tix (UsesAtuple tup) a = UsesAtuple (go tix tup)
  where
    go :: TupleIdx t' a -> Atuple UsesA t' -> Atuple UsesA t'
    go ZeroTupIdx      (SnocAtup t s) = t       `SnocAtup` (s +^ a)
    go (SuccTupIdx ix) (SnocAtup t s) = go ix t `SnocAtup` s

allA :: (Int -> Int -> Bool) -> UsesA a -> Bool
allA f (UsesAarray x y) = f x y
allA f (UsesAtuple tup) = go tup
  where
    go :: Atuple UsesA t -> Bool
    go NilAtup        = True
    go (SnocAtup t a) = go t && allA f a

asAtuple :: forall arrs. (Arrays arrs, IsAtuple arrs) => UsesA arrs -> Atuple UsesA (TupleRepr arrs)
asAtuple UsesAarray{}   = $internalError "asAtuple" "inconsistent valuation"
asAtuple (UsesAtuple t) = t


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
          | Just u   <- prjChain idx (inject pacc) oneD  -> u
          | Atuple t <- extract a                         -> countA (aprj tix t)
          | otherwise                                     -> countA a
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
      case flavour (undefined::s) of
        ArraysFarray -> countF' . reduceAccessFun idx
        _            -> countF'

    countE :: PreOpenExp acc env aenv e -> UsesA s
    countE =
      case flavour (undefined::s) of
        ArraysFarray -> countE' . reduceAccessExp idx
        _            -> countE'

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
      case extract a of
        Avar v | Just Refl <- match ix v  -> Just use
        Aprj ix' a'                       -> prjChain ix a' (useA ix' zero use)
        _                                 -> Nothing

    zero, oneS, oneD :: forall a. Arrays a => UsesA a
    zero  = init 0 0
    oneS  = init 1 0  -- shape
    oneD  = init 0 1  -- data

    init :: Arrays a => Int -> Int -> UsesA a
    init n m = goA
      where
        goA :: forall a. Arrays a => UsesA a
        goA =
          case flavour (undefined::a) of
            ArraysFarray -> UsesAarray n m
            ArraysFunit  -> UsesAtuple NilAtup
            ArraysFtuple -> UsesAtuple (goAT (prod (Proxy::Proxy Arrays) (undefined::a)))

        goAT :: ProdR Arrays a' -> Atuple UsesA a'
        goAT ProdRunit     = NilAtup
        goAT (ProdRsnoc p) = goAT p `SnocAtup` goA

