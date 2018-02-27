{-# LANGUAGE ConstraintKinds       #-}
{-# LANGUAGE DeriveDataTypeable    #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE StandaloneDeriving    #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE ViewPatterns          #-}
-- |
-- Module      : Data.Array.Accelerate.Trafo.Product
-- Copyright   : [2016..2018] Robert Clifton-Everest
-- License     : BSD3
--
-- Maintainer  : Trevor L. McDonell <tmcdonell@cse.unsw.edu.au>
-- Stability   : experimental
-- Portability : non-portable (GHC extensions)
--

module Data.Array.Accelerate.Trafo.Product
  where

import Data.Array.Accelerate.Array.Sugar
import Data.Array.Accelerate.Product

import Data.Typeable


-- A surface product type for any given product representation type.
--
-- As a part of various transformations, we need to be able to transform tuples
-- and other product types. Unfortunately, due to the way product types are
-- represented in Accelerate, with a non injective relationship between surface
-- types and representation types, this causes problems. Supposing we have
-- a tuple like so:
--
--   (a,b,c)
--
-- then suppose we want to pull b out of it, leaving us with (a,c). However, the
-- only way we can inspect the structure of a product is via its representation
-- type. That means we take:
--
--   ((((),a),b),c)
--
-- and produce:
--
--   (((),a),c)
--
-- But, what what should the corresponding surface type be for this new
-- representation type?
--
-- 'FreeProd' is a product type that gives a surface type for any product
-- representation type. That is:
--
--   forall t. FreeProd (ProdRepr t)
--
-- is a valid product type. Additionally:
--
--   forall t'. ProdRepr (FreeProd t') ~ t'
--
-- This gives us what we need in order to transform product types.
--
data FreeProd t where
  NilFreeProd  ::                                FreeProd ()
  SnocFreeProd :: Arrays s => FreeProd t -> s -> FreeProd (t,s)

deriving instance Typeable FreeProd

type IsAtupleRepr t = (Arrays (FreeProd t), Typeable t, IsAtuple (FreeProd t), t ~ ProdRepr (FreeProd t))

type instance ArrRepr (FreeProd (t,a)) = (ArrRepr (FreeProd t), ArrRepr a)
type instance ArrRepr (FreeProd ())    = ((),())

instance IsProduct Arrays (FreeProd ()) where
  type ProdRepr (FreeProd ()) = ()
  fromProd _ _ = ()
  toProd _ _   = NilFreeProd
  prod _ _     = ProdRunit

instance (IsProduct Arrays (FreeProd t), Arrays s) => IsProduct Arrays (FreeProd (t,s)) where
  type ProdRepr (FreeProd (t,s))  = (ProdRepr (FreeProd t), s)
  fromProd cst (SnocFreeProd t s) = (fromProd cst t, s)
  toProd cst (t,s)                = SnocFreeProd (toProd cst t) s
  prod cst _                      = ProdRsnoc (prod cst (undefined :: FreeProd t))

instance Arrays (FreeProd ()) where
  arrays  _ = ArraysRpair ArraysRunit ArraysRunit
  flavour _ = ArraysFtuple
  toArr   _ = NilFreeProd
  fromArr NilFreeProd = ((),())

instance (IsAtuple (FreeProd t), Typeable t, Arrays (FreeProd t), Arrays a) => Arrays (FreeProd (t,a)) where
  arrays  _   = arrays (undefined :: FreeProd t) `ArraysRpair` arrays (undefined :: a)
  flavour _   = ArraysFtuple
  toArr (t,a) = SnocFreeProd (toArr t) (toArr a)
  fromArr (SnocFreeProd t a) = (fromArr t, fromArr a)


-- Subproduct captures that a product representation t' can be extracted from
-- product representation t.
--
data Subproduct k t' t where
  NilSub ::                                                                      Subproduct k ()      ()
  InSub  :: (Arrays a, Arrays a') => Subproduct k t' t -> Subcomponent k a' a -> Subproduct k (t',a') (t,a)
  OutSub :: Arrays a              => Subproduct k t' t -> k a                 -> Subproduct k t'      (t,a)

-- Similar to above, this captures that a component of a tuple a contains
-- a "smaller" component a'.
--
data Subcomponent k a' a where
  AllSub   :: k a ->                                                            Subcomponent k a             a
  TupleSub :: (IsAtupleRepr t', IsAtuple a) => Subproduct k t' (TupleRepr a) -> Subcomponent k (FreeProd t') a

