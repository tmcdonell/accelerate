{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE PatternGuards       #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators       #-}
-- |
-- Module      : Data.Array.Accelerate.Trafo.Access
-- Copyright   : [2016..2018] Robert Clifton-Everest, Trevor L. McDonell
-- License     : BSD3
--
-- Maintainer  : Trevor L. McDonell <tmcdonell@cse.unsw.edu.au>
-- Stability   : experimental
-- Portability : non-portable (GHC extensions)o
--
-- Find and merge common array accesses
--

module Data.Array.Accelerate.Trafo.Access (

  -- Array access merging
  ReduceAccess,
  reduceAccessOpenAcc, reduceAccessPreAcc, reduceAccessAfun,
  reduceAccessExp, reduceAccessFun,

) where

-- standard library
import Prelude                                          hiding ( exp )

-- friends
import Data.Array.Accelerate.AST
import Data.Array.Accelerate.Array.Sugar
import Data.Array.Accelerate.Trafo.Base
import Data.Array.Accelerate.Trafo.Substitution


type ReduceAccess acc =
       forall aenv sh e arrs. (Shape sh, Elt e)
    => Idx aenv (Array sh e)
    -> acc aenv arrs
    -> acc aenv arrs

reduceAccessOpenAcc
    :: (Shape sh, Elt e)
    => Idx aenv (Array sh e)
    -> OpenAcc aenv arrs
    -> OpenAcc aenv arrs
reduceAccessOpenAcc idx (OpenAcc pacc) =
  OpenAcc (reduceAccessPreAcc reduceAccessOpenAcc idx pacc)

reduceAccessPreAcc
    :: forall acc aenv arrs sh e. (Kit acc, Shape sh, Elt e)
    => ReduceAccess acc
    -> Idx aenv (Array sh e)
    -> PreOpenAcc acc aenv arrs
    -> PreOpenAcc acc aenv arrs
reduceAccessPreAcc reduceAcc idx = \case
  Alet bnd body             -> Alet (cvtA bnd) (reduceAcc (SuccIdx idx) body)
  Avar ix                   -> Avar ix
  Atuple tup                -> Atuple (cvtAT tup)
  Aprj tup a                -> Aprj tup (cvtA a)
  Apply f a                 -> Apply (cvtAF f) (cvtA a)
  Aforeign ff afun acc      -> Aforeign ff afun (cvtA acc)
  Acond p t e               -> Acond (cvtE p) (cvtA t) (cvtA e)
  Awhile p f a              -> Awhile (cvtAF p) (cvtAF f) (cvtA a)
  Use a                     -> Use a
  Unit e                    -> Unit (cvtE e)
  Reshape e a               -> Reshape (cvtE e) (cvtA a)
  Generate e f              -> Generate (cvtE e) (cvtF f)
  Transform sh ix f a       -> Transform (cvtE sh) (cvtF ix) (cvtF f) (cvtA a)
  Replicate sl slix a       -> Replicate sl (cvtE slix) (cvtA a)
  Slice sl a slix           -> Slice sl (cvtA a) (cvtE slix)
  Map f a                   -> Map (cvtF f) (cvtA a)
  ZipWith f a1 a2           -> ZipWith (cvtF f) (cvtA a1) (cvtA a2)
  Fold f z a                -> Fold (cvtF f) (cvtE z) (cvtA a)
  Fold1 f a                 -> Fold1 (cvtF f) (cvtA a)
  FoldSeg f z a s           -> FoldSeg (cvtF f) (cvtE z) (cvtA a) (cvtA s)
  Fold1Seg f a s            -> Fold1Seg (cvtF f) (cvtA a) (cvtA s)
  Scanl f z a               -> Scanl (cvtF f) (cvtE z) (cvtA a)
  Scanl' f z a              -> Scanl' (cvtF f) (cvtE z) (cvtA a)
  Scanl1 f a                -> Scanl1 (cvtF f) (cvtA a)
  Scanr f z a               -> Scanr (cvtF f) (cvtE z) (cvtA a)
  Scanr' f z a              -> Scanr' (cvtF f) (cvtE z) (cvtA a)
  Scanr1 f a                -> Scanr1 (cvtF f) (cvtA a)
  Permute f1 a1 f2 a2       -> Permute (cvtF f1) (cvtA a1) (cvtF f2) (cvtA a2)
  Backpermute sh f a        -> Backpermute (cvtE sh) (cvtF f) (cvtA a)
  Stencil f b a             -> Stencil (cvtF f) (cvtB b) (cvtA a)
  Stencil2 f b1 a1 b2 a2    -> Stencil2 (cvtF f) (cvtB b1) (cvtA a1) (cvtB b2) (cvtA a2)
  where
    cvtA :: acc aenv a -> acc aenv a
    cvtA = reduceAcc idx

    cvtAF :: PreOpenAfun acc aenv t -> PreOpenAfun acc aenv t
    cvtAF = reduceAccessAfun reduceAcc idx

    cvtAT :: Atuple (acc aenv) t -> Atuple (acc aenv) t
    cvtAT NilAtup        = NilAtup
    cvtAT (SnocAtup t a) = SnocAtup (cvtAT t) (cvtA a)

    cvtB :: PreBoundary acc aenv a -> PreBoundary acc aenv a
    cvtB Clamp        = Clamp
    cvtB Mirror       = Mirror
    cvtB Wrap         = Wrap
    cvtB (Constant c) = Constant c
    cvtB (Function f) = Function (cvtF f)

    cvtE :: PreOpenExp acc env aenv e' -> PreOpenExp acc env aenv e'
    cvtE = reduceAccessExp idx

    cvtF :: PreOpenFun acc env aenv e' -> PreOpenFun acc env aenv e'
    cvtF = reduceAccessFun idx


reduceAccessAfun
    :: (Shape sh, Elt e)
    => ReduceAccess acc
    -> Idx aenv (Array sh e)
    -> PreOpenAfun acc aenv f
    -> PreOpenAfun acc aenv f
reduceAccessAfun reduceAcc idx (Abody a) = Abody (reduceAcc idx a)
reduceAccessAfun reduceAcc idx (Alam f)  = Alam  (reduceAccessAfun reduceAcc (SuccIdx idx) f)

reduceAccessExp
    :: (Kit acc, Shape sh, Elt e)
    => Idx aenv (Array sh e)
    -> PreOpenExp acc env aenv t
    -> PreOpenExp acc env aenv t
reduceAccessExp idx exp =
  case elimArrayAccess idx exp of
    Left (sh, e) -> inline e (Index (inject $ Avar idx) sh)
    Right e      -> e

reduceAccessFun
    :: (Kit acc, Shape sh, Elt e)
    => Idx aenv (Array sh e)
    -> PreOpenFun acc env aenv f
    -> PreOpenFun acc env aenv f
reduceAccessFun ix (Body b) = Body (reduceAccessExp ix b)
reduceAccessFun ix (Lam f)  = Lam  (reduceAccessFun ix f)

elimArrayAccess
    :: forall acc env aenv sh e e'. (Kit acc, Elt e, Shape sh)
    => Idx aenv (Array sh e)
    -> PreOpenExp acc env aenv e'
    -> Either (PreOpenExp acc env aenv sh, PreOpenExp acc (env,e) aenv e') (PreOpenExp acc env aenv e')
elimArrayAccess idx = \case
  Let bnd body        -> cvtLet (cvtE bnd) (cvtE body)
  Var ix              -> noAccess (Var ix)
  Const c             -> noAccess (Const c)
  Undef               -> noAccess Undef
  IndexAny            -> noAccess IndexAny
  IndexNil            -> noAccess IndexNil
  Tuple tup           -> cvtT tup
  Prj tup e           -> cvtE1 (Prj tup)      (cvtE e)
  IndexCons sh sz     -> cvtE2 IndexCons      (cvtE sh) (cvtE sz)
  IndexHead sh        -> cvtE1 IndexHead      (cvtE sh)
  IndexTail sh        -> cvtE1 IndexTail      (cvtE sh)
  IndexSlice x ix sh  -> cvtE2 (IndexSlice x) (cvtE ix) (cvtE sh)
  IndexFull x ix sl   -> cvtE2 (IndexFull x)  (cvtE ix) (cvtE sl)
  ToIndex sh ix       -> cvtE2 ToIndex        (cvtE sh) (cvtE ix)
  FromIndex sh ix     -> cvtE2 FromIndex      (cvtE sh) (cvtE ix)
  Cond p t e          -> cvtE3 Cond           (cvtE p) (cvtE t) (cvtE e)
  While p f x         -> cvtE3 While          (cvtF p) (cvtF f) (cvtE x)
  PrimApp f x         -> cvtE1 (PrimApp f)    (cvtE x)
  PrimConst c         -> noAccess (PrimConst c)
  Shape a             -> noAccess (Shape a)
  ShapeSize sh        -> cvtE1 ShapeSize      (cvtE sh)
  Intersect sh th     -> cvtE2 Intersect      (cvtE sh) (cvtE th)
  Union sh th         -> cvtE2 Union          (cvtE sh) (cvtE th)
  Foreign ff f e      -> cvtE1 (Foreign ff f) (cvtE e)

  Index a sh
    | Avar idx' <- extract a
    , Just Refl <- match idx idx' -> Left (sh, Var ZeroIdx)
    | otherwise                   -> Index a `cvtE1` cvtE sh

  LinearIndex a i
    | Avar idx' <- extract a
    , Just Refl <- match idx idx' -> Left (FromIndex (Shape a) i, Var ZeroIdx)
    | otherwise                   -> LinearIndex a `cvtE1` cvtE i

  where
    cvtE :: PreOpenExp acc env' aenv t
         -> Either (PreOpenExp acc env' aenv sh, PreOpenExp acc (env', e) aenv t) (PreOpenExp acc env' aenv t)
    cvtE = elimArrayAccess idx

    cvtF :: PreOpenFun acc env aenv (a -> b)
         -> Either (PreOpenExp acc env aenv sh, PreOpenFun acc (env,e) aenv (a -> b)) (PreOpenFun acc env aenv (a -> b))
    cvtF (Lam (Body b)) =
      case cvtE b of
        Left (sh, e)
          | Just sh' <- strengthenE noTop sh  -> Left (sh', Lam (Body (weakenE swapTop e)))
          | otherwise                         -> Right (Lam (Body (inline e (access sh))))
        Right b'                              -> Right (Lam (Body b'))
    cvtF _ = error "That thing out there... That is no dinosaur"

    cvtE1 :: (forall env'. PreOpenExp acc env' aenv s -> PreOpenExp acc env' aenv t)
          -> Either (PreOpenExp acc env aenv sh, PreOpenExp acc (env,e) aenv s) (PreOpenExp acc env aenv s)
          -> Either (PreOpenExp acc env aenv sh, PreOpenExp acc (env,e) aenv t) (PreOpenExp acc env aenv t)
    cvtE1 f (Left (sh, e)) = Left (sh, f e)
    cvtE1 f (Right e)      = Right (f e)

    cvtE2 :: (Elt a, Elt s, Elt t)
          => (forall env'. PreOpenExp acc env' aenv s -> PreOpenExp acc env' aenv t -> PreOpenExp acc env' aenv a)
          -> Either (PreOpenExp acc env aenv sh, PreOpenExp acc (env,e) aenv s) (PreOpenExp acc env aenv s)
          -> Either (PreOpenExp acc env aenv sh, PreOpenExp acc (env,e) aenv t) (PreOpenExp acc env aenv t)
          -> Either (PreOpenExp acc env aenv sh, PreOpenExp acc (env,e) aenv a) (PreOpenExp acc env aenv a)
    cvtE2 f (Right s)     (Right t)      = Right (f s t)
    cvtE2 f (Right s)     (Left (e, t))  = Left (e, f (weakenE SuccIdx s) t)
    cvtE2 f (Left (e, s)) (Left (e', t))
      | Just Refl <- match e e'          = Left (e, Let (Var ZeroIdx) (f (weakenE oneBelow s) (weakenE oneBelow t)))
      | otherwise                        = Right (f (inline s (access e)) (inline t (access e')))
    cvtE2 f s             t              = cvtE2 (flip f) t s

    cvtE3 :: ( Elt a
             , SinkExp f, RebuildableExp f, acc ~ AccCloE f
             , SinkExp g, RebuildableExp g, acc ~ AccCloE g
             , SinkExp h, RebuildableExp h, acc ~ AccCloE h
             )
          => (forall env'. f env' aenv r -> g env' aenv s -> h env' aenv t -> PreOpenExp acc env' aenv a)
          -> Either (PreOpenExp acc env aenv sh, f (env,e) aenv r) (f env aenv r)
          -> Either (PreOpenExp acc env aenv sh, g (env,e) aenv s) (g env aenv s)
          -> Either (PreOpenExp acc env aenv sh, h (env,e) aenv t) (h env aenv t)
          -> Either (PreOpenExp acc env aenv sh, PreOpenExp acc (env,e) aenv a) (PreOpenExp acc env aenv a)
    cvtE3 f (Right r) (Right s)     (Right t)      = Right (f r s t)
    cvtE3 f (Right r) (Right s)     (Left (e, t))  = Left (e, f (weakenE SuccIdx r) (weakenE SuccIdx s) t)
    cvtE3 f r@Right{} s@Left{}      t@Right{}      = cvtE3 (flip . f) r t s
    cvtE3 f r@Left{}  s@Right{}     t@Right{}      = cvtE3 (flip f) s r t
    cvtE3 f (Right r) (Left (e, s)) (Left (e', t))
      | Just Refl <- match e e'                    = Left (e, Let (Var ZeroIdx) $ f (weakenE (SuccIdx . SuccIdx) r) (weakenE oneBelow s) (weakenE oneBelow t))
      | otherwise                                  = Right (f r (inline s (access e)) (inline t (access e')))
    cvtE3 f r@Left{}  s@Right{}     t@Left{}       = cvtE3 (flip f) s r t
    cvtE3 f r@Left{}  s@Left{}      t@Right{}      = cvtE3 (flip . f) r t s
    cvtE3 f (Left (e,r)) (Left (e', s)) (Left (e'', t))
      | Just Refl <- match e e'
      , Just Refl <- match e' e''
      = Left (e, Let (Var ZeroIdx) $ f (weakenE oneBelow r) (weakenE oneBelow s) (weakenE oneBelow t))
      | otherwise
      = Right (f (inline r (access e)) (inline s (access e)) (inline t (access e')))

    cvtLet
        :: (Elt s, Elt t)
        => Either (PreOpenExp acc env aenv sh,     PreOpenExp acc (env,e) aenv s)     (PreOpenExp acc env aenv s)
        -> Either (PreOpenExp acc (env,s) aenv sh, PreOpenExp acc ((env,s),e) aenv t) (PreOpenExp acc (env,s) aenv t)
        -> Either (PreOpenExp acc env aenv sh,     PreOpenExp acc (env,e) aenv t)     (PreOpenExp acc env aenv t)
    cvtLet (Right s) (Right t)            = Right (Let s t)
    cvtLet (Right s) (Left (e, t))
      | Just e' <- strengthenE noTop e    = Left  (e', Let (weakenE SuccIdx s) (weakenE swapTop t))
      | otherwise                         = Right (Let s (inline t (access e)))
    cvtLet (Left (e, s)) (Right t)        = Left (e, Let s (weakenE (swapTop . SuccIdx) t))
    cvtLet (Left (e, s)) (Left (e', t))
      | Just e''  <- strengthenE noTop e'
      , Just Refl <- match e e''          = Left (e, Let (Var ZeroIdx) $ Let (weakenE oneBelow s) (weakenE (under oneBelow . swapTop) t))
      | otherwise                         = Right (Let (inline s (access e)) (inline t (access e')))

    cvtT :: (Elt t, IsTuple t)
         => Tuple (PreOpenExp acc env aenv) (TupleRepr t)
         -> Either (PreOpenExp acc env aenv sh, PreOpenExp acc (env,e) aenv t) (PreOpenExp acc env aenv t)
    cvtT tup =
      case go tup of
        Left (sh, t, True)  -> Left (sh, Let (Var ZeroIdx) (weakenE oneBelow (Tuple t)))
        Left (sh, t, False) -> Left (sh, Tuple t)
        Right t             -> Right (Tuple t)
      where
        go :: Tuple (PreOpenExp acc env aenv) t
           -> Either (PreOpenExp acc env aenv sh, Tuple (PreOpenExp acc (env,e) aenv) t, Bool) (Tuple (PreOpenExp acc env aenv) t)
        go NilTup        = Right NilTup
        go (SnocTup t e) =
          case (go t, cvtE e) of
            (Right t', Right e')                  -> Right (t' `SnocTup` e')
            (Right t', Left (sh, e'))             -> Left (sh, (unRTup . weakenE SuccIdx . RebuildTup) t' `SnocTup` e', False)
            (Left (sh, t', dups), Right e')       -> Left (sh, t' `SnocTup` weakenE SuccIdx e', dups)
            (Left (sh, t', _),    Left (sh', e'))
              | Just Refl <- match sh sh'         -> Left (sh, t' `SnocTup` e', True)
              | otherwise                         -> Right (unRTup (inline (RebuildTup t') (access sh)) `SnocTup` inline e' (access sh'))

    oneBelow :: (env', a) :> ((env', b), a)
    oneBelow ZeroIdx      = ZeroIdx
    oneBelow (SuccIdx ix) = SuccIdx (SuccIdx ix)

    swapTop :: ((env', a), b) :> ((env', b), a)
    swapTop ZeroIdx                = SuccIdx ZeroIdx
    swapTop (SuccIdx ZeroIdx)      = ZeroIdx
    swapTop (SuccIdx (SuccIdx ix)) = SuccIdx (SuccIdx ix)

    under :: env1 :> env2 -> (env1, a) :> (env2, a)
    under _ ZeroIdx      = ZeroIdx
    under v (SuccIdx ix) = SuccIdx (v ix)

    noTop :: (env', a) :?> env'
    noTop ZeroIdx      = Nothing
    noTop (SuccIdx ix) = Just ix

    access :: PreOpenExp acc env' aenv sh -> PreOpenExp acc env' aenv e
    access = Index (inject (Avar idx))

    noAccess :: PreOpenExp acc env aenv e' -> Either no (PreOpenExp acc env aenv e')
    noAccess = Right

