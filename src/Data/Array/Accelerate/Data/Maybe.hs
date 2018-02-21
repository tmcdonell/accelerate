{-# LANGUAGE CPP                   #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PatternGuards         #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE UndecidableInstances  #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
-- |
-- Module      : Data.Array.Accelerate.Data.Maybe
-- Copyright   : [2018] Trevor L. McDonell
-- License     : BSD3
--
-- Maintainer  : Trevor L. McDonell <tmcdonell@cse.unsw.edu.au>
-- Stability   : experimental
-- Portability : non-portable (GHC extensions)
--
-- @since 1.2.0.0
--

module Data.Array.Accelerate.Data.Maybe (

  Maybe(..),
  just, nothing,
  maybe, isJust, isNothing, fromMaybe, fromJust, justs,

) where

import Data.Array.Accelerate.Analysis.Match
import Data.Array.Accelerate.Array.Sugar                            hiding ( (!), shape, ignore, toIndex )
import Data.Array.Accelerate.Language                               hiding ( chr )
import Data.Array.Accelerate.Prelude                                hiding ( filter )
import Data.Array.Accelerate.Product
import Data.Array.Accelerate.Smart
import Data.Array.Accelerate.Type

import Data.Array.Accelerate.Classes.Eq
import Data.Array.Accelerate.Classes.Num
import Data.Array.Accelerate.Classes.Ord

import Data.Array.Accelerate.Data.Functor
import Data.Array.Accelerate.Data.Monoid
#if __GLASGOW_HASKELL__ >= 800
import Data.Array.Accelerate.Data.Semigroup
#endif

import Data.Char
import Data.Maybe                                                   ( Maybe(..) )
import Data.Typeable
import Foreign.C.Types
import Prelude                                                      ( (.), ($), const, undefined, otherwise )


-- | Lift a value into a 'Just' constructor
--
just :: Elt a => Exp a -> Exp (Maybe a)
just x = lift (Just x)

-- | The 'Nothing' constructor
--
nothing :: forall a. Elt a => Exp (Maybe a)
nothing = lift (Nothing :: Maybe (Exp a))
--
-- Note: [lifting Nothing]
--
-- The lift instance for 'Nothing' uses our magic 'undef' term, meaning that our
-- backends will know that we can leave this slot in the values array undefined.
-- If we had instead written 'constant Nothing' this would result in writing an
-- actual (unspecified) value into the values array, which is what we want to
-- avoid.
--

-- | Returns 'True' if the argument is 'Nothing'
--
isNothing :: Elt a => Exp (Maybe a) -> Exp Bool
isNothing x = tag x == 0

-- | Returns 'True' if the argument is of the form @Just _@
--
isJust :: Elt a => Exp (Maybe a) -> Exp Bool
isJust x = tag x == 1

-- | The 'fromMaybe' function takes a default value and a 'Maybe' value. If the
-- 'Maybe' is 'Nothing', the default value is returned; otherwise, it returns
-- the value contained in the 'Maybe'.
--
fromMaybe :: Elt a => Exp a -> Exp (Maybe a) -> Exp a
fromMaybe d x = cond (isNothing x) d (fromJust x)

-- | The 'fromJust' function extracts the element out of the 'Just' constructor.
-- If the argument was actually 'Nothing', you will get an undefined value
-- instead.
--
fromJust :: Elt a => Exp (Maybe a) -> Exp a
fromJust x = Exp $ ZeroTupIdx `Prj` x

-- | The 'maybe' function takes a default value, a function, and a 'Maybe'
-- value. If the 'Maybe' value is nothing, the default value is returned;
-- otherwise, it applies the function to the value inside the 'Just' and returns
-- the result
--
maybe :: (Elt a, Elt b) => Exp b -> (Exp a -> Exp b) -> Exp (Maybe a) -> Exp b
maybe d f x = cond (isNothing x) d (f (fromJust x))


-- | Extract from an array all of the 'Just' values, together with a segment
-- descriptor indicating how many elements along each dimension were returned.
--
justs :: (Shape sh, Slice sh, Elt a)
      => Acc (Array (sh:.Int) (Maybe a))
      -> Acc (Vector a, Array sh Int)
justs xs = filter' (map isJust xs) (map fromJust xs)


instance Functor Maybe where
  fmap f x = cond (isNothing x) (constant Nothing) (lift (Just (f (fromJust x))))

instance Eq a => Eq (Maybe a) where
  ma == mb = cond (isNothing ma && isNothing mb) (constant True)
           $ cond (isJust ma    && isJust mb)    (fromJust ma == fromJust mb)
           $ constant False

instance Ord a => Ord (Maybe a) where
  compare ma mb = cond (isJust ma && isJust mb)
                       (compare (fromJust ma) (fromJust mb))
                       (compare (tag ma) (tag mb))

instance (Monoid (Exp a), Elt a) => Monoid (Exp (Maybe a)) where
  mempty        = constant Nothing
  mappend ma mb = cond (isNothing ma) mb
                $ cond (isNothing mb) ma
                $ lift (Just (fromJust ma `mappend` fromJust mb))

#if __GLASGOW_HASKELL__ >= 800
instance (Semigroup (Exp a), Elt a) => Semigroup (Exp (Maybe a)) where
  ma <> mb = cond (isNothing ma) mb
           $ cond (isNothing mb) mb
           $ lift (Just (fromJust ma <> fromJust mb))
#endif


tag :: Elt a => Exp (Maybe a) -> Exp Word8
tag x = Exp $ SuccTupIdx ZeroTupIdx `Prj` x


type instance EltRepr (Maybe a) = TupleRepr (Word8, EltRepr a)

instance Elt a => Elt (Maybe a) where
  eltType _        = eltType (undefined::(Word8,a))
  toElt (((),0),_) = Nothing
  toElt (_     ,x) = Just (toElt x)
  fromElt Nothing  = (((),0), undef' (eltType (undefined::a)))
  fromElt (Just a) = (((),1), fromElt a)

instance Elt a => IsProduct Elt (Maybe a) where
  type ProdRepr (Maybe a) = ProdRepr (Word8, a)
  toProd _ (((),0),_) = Nothing
  toProd _ (_,     x) = Just x
  fromProd _ Nothing  = (((), 0), toElt (undef' (eltType (undefined::a))))
  fromProd _ (Just a) = (((), 1), a)
  prod cst _ = prod cst (undefined :: (Word8,a))

instance (Lift Exp a, Elt (Plain a)) => Lift Exp (Maybe a) where
  type Plain (Maybe a) = Maybe (Plain a)
  lift Nothing  = Exp . Tuple $ NilTup `SnocTup` constant 0 `SnocTup` undef
  lift (Just x) = Exp . Tuple $ NilTup `SnocTup` constant 1 `SnocTup` lift x


-- Utilities
-- ---------

-- We need an undefined value for the Nothing case. We just fill this with
-- zeros, though it would be better if we can actually do nothing, and leave
-- those value in memory undefined.
--
undef' :: TupleType t -> t
undef' TypeRunit         = ()
undef' (TypeRpair ta tb) = (undef' ta, undef' tb)
undef' (TypeRscalar s)   = scalar s

scalar :: ScalarType t -> t
scalar (SingleScalarType t) = single t
scalar (VectorScalarType t) = vector t

single :: SingleType t -> t
single (NumSingleType    t) = num t
single (NonNumSingleType t) = nonnum t

vector :: VectorType t -> t
vector (Vector2Type t)  = let x = single t in V2 x x
vector (Vector3Type t)  = let x = single t in V3 x x x
vector (Vector4Type t)  = let x = single t in V4 x x x x
vector (Vector8Type t)  = let x = single t in V8 x x x x x x x x
vector (Vector16Type t) = let x = single t in V16 x x x x x x x x x x x x x x x x

num :: NumType t -> t
num (IntegralNumType t) | IntegralDict <- integralDict t = 0
num (FloatingNumType t) | FloatingDict <- floatingDict t = 0

nonnum :: NonNumType t -> t
nonnum TypeBool{}   = False
nonnum TypeChar{}   = chr 0
nonnum TypeCChar{}  = CChar 0
nonnum TypeCSChar{} = CSChar 0
nonnum TypeCUChar{} = CUChar 0


filter'
    :: forall sh e. (Shape sh, Slice sh, Elt e)
    => Acc (Array (sh:.Int) Bool)     -- tags
    -> Acc (Array (sh:.Int) e)        -- values
    -> Acc (Vector e, Array sh Int)
filter' keep arr
  | Just Refl <- matchShapeType (undefined::sh) (undefined::Z)
  = let
        (target, len)   = unlift $ scanl' (+) 0 (map boolToInt keep)
        prj ix          = keep!ix ? ( index1 (target!ix), ignore )
        dummy           = fill (index1 (the len)) undef
        result          = permute const dummy prj arr
    in
    null keep ?| ( lift (emptyArray, fill (constant Z) 0)
                 , lift (result, len)
                 )
  | otherwise
  = let
        sz              = indexTail (shape arr)
        (target, len)   = unlift $ scanl' (+) 0 (map boolToInt keep)
        (offset, valid) = unlift $ scanl' (+) 0 (flatten len)
        prj ix          = cond (keep!ix)
                               (index1 $ offset!index1 (toIndex sz (indexTail ix)) + target!ix)
                               ignore
        dummy           = fill (index1 (the valid)) undef
        result          = permute const dummy prj arr
    in
    null keep ?| ( lift (emptyArray, fill sz 0)
                 , lift (result, len)
                 )

emptyArray :: (Shape sh, Elt e) => Acc (Array sh e)
emptyArray = fill (constant empty) undef

