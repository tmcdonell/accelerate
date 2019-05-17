{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE TypeFamilies        #-}
{-# LANGUAGE TypeOperators       #-}
{-# OPTIONS_GHC -fno-warn-incomplete-patterns #-}  -- pattern synonyms
-- |
-- Module      : Data.Array.Accelerate.Sequence
-- Copyright   : [2008..2019] The Accelerate Team
-- License     : BSD3
--
-- Maintainer  : Trevor L. McDonell <trevor.mcdonell@gmail.com>
-- Stability   : experimental
-- Portability : non-portable (GHC extensions)
--
-- Operations over (possibly infinite) sequences of arrays. This module is
-- meant to be imported qualified.
--

module Data.Array.Accelerate.Sequence (

  -- * Sequence expressions
  Seq, Acc, Exp,                        -- re-exporting from 'Smart'

  -- ** Evaluation
  collect,

  -- ** Producing sequences
  streamIn, subarrays, segments,
  slice, sliceInner, sliceOuter,
  generate,
  -- fromShapes, fromOffsets,

  -- ** Element-wise operations
  -- *** Mapping
  map,

  -- *** Zipping
  zipWith, zipWith3, zipWith4, zipWith5, zipWith6, zipWith7, zipWith8, zipWith9,
  zip, zip3, zip4, zip5, zip6, zip7, zip8, zip9,

  -- *** Unzipping
  unzip, unzip3, unzip4, unzip5, unzip6, unzip7, unzip8, unzip9,

  -- ** Combining sequences
  tabulate, elements, shapes,

  -- ** Folding
  fold,

) where

import Data.Array.Accelerate.Analysis.Match
import Data.Array.Accelerate.Array.Sugar                            hiding ( (!!), size, shape, toSlice )
import Data.Array.Accelerate.Lift
import Data.Array.Accelerate.Pattern
import Data.Array.Accelerate.Smart
import Data.Array.Accelerate.Type

import Data.Array.Accelerate.Classes.Num

import Data.Array.Accelerate.Language                               ( (!!), unit, size, shape, shapeSize, indexHead, indexFull, indexSlice, toSlice )
import Data.Array.Accelerate.Prelude                                ( afst, asnd, curry, the )
import qualified Data.Array.Accelerate.Language                     as A

import Prelude                                                      ( (.), Maybe(..), otherwise )


-- Producing sequences
-- -------------------

-- | Force a sequence computation to be evaluated, until all the input is
-- consumed and the final result calculated.
--
collect :: Arrays arrs => Seq arrs -> Acc arrs
collect = Acc . Collect

-- | Produce a sequence by lazily consuming elements from the input list.
--
-- XXX: The implementation should check whether the elements
-- consumed/pulled for each computation step are of the same extent, and
-- execute a regular computation if so.
--
streamIn :: (Shape sh, Elt e) => [Array sh e] -> Seq [Array sh e]
streamIn = Seq . StreamIn


-- | Sequence an array by slicing it according to the given specification.
-- The given slice index represents the starting point of the subdivisions,
-- with the sequence yielding each subsequent slice.
--
-- XXX: Add example
--
slice :: forall slix e. (Slice slix, Elt e)
      => Exp slix
      -> Acc (Array (FullShape  slix) e)
      -> Seq [Array (SliceShape slix) e]
slice slix arr = generate slices (A.slice arr . toSlice slix sh . the)
  where
    sh = shape arr

    -- XXX: This is a bit strange..
    slices :: Exp Int
    slices = total - sofar
      where
        sofar                                               = shapeSize (indexFull  slix  sl)
        total | ASlice slix' <- fullShape (sliceType @slix) = shapeSize (indexSlice slix' sh)

        sl :: Exp (SliceShape slix)
        sl = go (shapeType @(SliceShape slix))
          where
            go :: ShapeR t -> Exp t
            go ShapeRnil        = Z_
            go (ShapeRcons shR) = go shR ::. 1

    fullShape :: forall sl. Slice sl => SliceR sl -> ASlice (FullShape sl)
    fullShape SliceRnil                                      = ASlice Z_
    fullShape (SliceRall   slR) | ASlice sl <- fullShape slR = ASlice (sl ::. constant @Int 0)
    fullShape (SliceRfixed slR) | ASlice sl <- fullShape slR = ASlice (sl ::. constant All)
    fullShape SliceRany         | IsSlice   <- isSlice (shapeType @(FullShape sl)) = ASlice anyShape
      where
        isSlice :: ShapeR sh -> IsSlice sh
        isSlice ShapeRnil                                 = IsSlice
        isSlice (ShapeRcons shR) | IsSlice <- isSlice shR = IsSlice

    anyShape :: forall s t. (t ~ Any s, Shape s) => Exp s
    anyShape = go (shapeType @s)
      where
        go :: ShapeR u -> Exp u
        go ShapeRnil        = Z_
        go (ShapeRcons shR) = go shR ::. 0

data ASlice sh where
  ASlice :: (Slice slix, FullShape slix ~ sh) => Exp slix -> ASlice sh

data IsSlice sh where
  IsSlice :: Slice sh => IsSlice sh


-- | Sequence an array by splitting it on the innermost dimension
--
-- XXX: Add example
--
sliceInner
    :: forall sh e. (Shape sh, Slice sh, Elt e)
    => Acc (Array (sh:.Int) e)
    -> Seq [Array sh e]
sliceInner arr
  | Just Refl <- matchShapeType @sh @Z = generate (size arr)              (\i -> unit (arr !! the i))
  | otherwise                          = generate (indexHead (shape arr)) (\i -> A.slice arr (lift (Any :. the i)))

-- | Sequence an array by splitting it on the outermost dimension
--
-- XXX: Add example
--
sliceOuter
    :: forall sh e. (Shape sh, Slice sh, Elt e)
    => Acc (Array (sh:.Int) e)
    -> Seq [Array sh e]
sliceOuter arr
  | Just Refl <- matchShapeType @(SliceShape (sh:.Int)) @sh
  , Just Refl <- matchShapeType @(FullShape  (sh:.Int)) @(sh:.Int)
  = generate n (A.slice arr . slix (shapeType @sh) . the)
  where
    n = innermost shapeType (shape arr)
          where
            innermost :: ShapeR (t :. Int) -> Exp (t :. Int) -> Exp Int
            innermost (ShapeRcons     ShapeRnil)    (Z_ ::. i) = i
            innermost (ShapeRcons shR@ShapeRcons{}) (sh ::. _) = innermost shR sh

    slix :: ShapeR t -> Exp Int -> Exp (SliceOuter t)
    slix ShapeRnil        i                      = Z_         ::. i
    slix (ShapeRcons shR) i | IsElt <- isElt shR = slix shR i ::. constant All

    isElt :: ShapeR t -> IsElt (SliceOuter t)
    isElt ShapeRnil                             = IsElt
    isElt (ShapeRcons shR) | IsElt <- isElt shR = IsElt

data IsElt t where
  IsElt :: Elt t => IsElt t

type family SliceOuter sh where
  SliceOuter Z           = Z             :. Int
  SliceOuter (sh :. Int) = SliceOuter sh :. All


-- | Split an array up into subarrays of the given shape along the
-- outermost dimension, moving inward.
--
-- For example, for a two-dimensional input array, the returned sequence
-- consists of the sub-matrices in column-major order.
--
-- XXX: Add a concrete example
-- TLM: column-major, huh?
--
subarrays
    :: (Shape sh, Elt e, sh :<= DIM2)
    => Exp sh
    -> Array sh e
    -> Seq [Array sh e]
subarrays = Seq $$ Subarrays

-- | Generate a sequence from a segmented array, given the segment
-- descriptor (in (offset, shape) format) and the vector of values.
--
-- XXX: This representation is not consistent with foldSeg, which takes
-- only the size of each segment from which we calculate the offsets.
--
-- XXX: Why do we need the second parameter? Why is this not just the
-- length of the segment descriptor ('drop' is free after all)
--
segments
    :: (Shape sh, Elt e)
    => Acc (Segments (Int,sh))  -- ^ Segments
    -> Exp Int                  -- ^ Take this many segments
    -> Acc (Vector e)           -- ^ The flattened values vector
    -> Seq [Array sh e]
segments = Seq $$$ FromSegs

-- | Generate a sequence by applying a function at every index.
--
-- XXX: This is the sequence equivalent of 'generate'. It sort of makes
-- sense that it is one dimensional, because the resulting sequence is
-- list-like, but I think it can freely be generalised to Shape.
--
generate
    :: Arrays a
    => Exp Int
    -> (Acc (Scalar Int) -> Acc a)
    -> Seq [a]
generate = Seq $$ Produce


{--
-- | Produce a sequence from shape segments and a flattened vector of values.
--
fromShapes :: (Shape sh, Elt e) => Acc (Segments sh) -> Acc (Vector e) -> Seq [Array sh e]
fromShapes shs = fromSegs (zip offs shs) (length shs)
  where
    offs = afst $ scanl' (+) 0 (map shapeSize shs)

-- | Produce a sequence from shape segments and a flattened vector of values.
--
fromOffsets :: Elt e => Acc (Segments Int) -> Acc (Vector e) -> Seq [Vector e]
fromOffsets offs vs = fromSegs (zip offs shs) (length offs) vs
  where
    ts  = length vs
    shs = map index1 (zipWith (-) (offs ++ flatten (unit ts)) offs)
--}


-- Element-wise operations
-- -----------------------

-- | Apply the given function to every element of the sequence.
--
-- XXX: Add example
--
map :: (Arrays a, Arrays b)
    => (Acc a -> Acc b)
    -> Seq [a]
    -> Seq [b]
map = Seq $$ MapSeq

-- | Apply the given binary function element-wise to the two sequences.
-- The length of the resulting sequence is the minumum of the lengths of
-- the two source sequences.
--
-- XXX: Add example
--
zipWith :: (Arrays a, Arrays b, Arrays c)
        => (Acc a -> Acc b -> Acc c)
        -> Seq [a]
        -> Seq [b]
        -> Seq [c]
zipWith = Seq $$$ ZipWithSeq

-- | Combine three sequences using the given function, analogous to
-- 'zipWith'.
--
zipWith3
    :: (Arrays a, Arrays b, Arrays c, Arrays d)
    => (Acc a -> Acc b -> Acc c -> Acc d)
    -> Seq [a]
    -> Seq [b]
    -> Seq [c]
    -> Seq [d]
zipWith3 op as bs cs =
  map (\(T3 a b c) -> op a b c) (zip3 as bs cs)

-- | Combine four sequences using the given function, analogous to
-- 'zipWith'.
--
zipWith4
    :: (Arrays a, Arrays b, Arrays c, Arrays d, Arrays e)
    => (Acc a -> Acc b -> Acc c -> Acc d -> Acc e)
    -> Seq [a]
    -> Seq [b]
    -> Seq [c]
    -> Seq [d]
    -> Seq [e]
zipWith4 op as bs cs ds =
  map (\(T4 a b c d) -> op a b c d) (zip4 as bs cs ds)

-- | Combine five sequences using the given function, analogous to
-- 'zipWith'.
--
zipWith5
    :: (Arrays a, Arrays b, Arrays c, Arrays d, Arrays e, Arrays f)
    => (Acc a -> Acc b -> Acc c -> Acc d -> Acc e -> Acc f)
    -> Seq [a]
    -> Seq [b]
    -> Seq [c]
    -> Seq [d]
    -> Seq [e]
    -> Seq [f]
zipWith5 op as bs cs ds es =
  map (\(T5 a b c d e) -> op a b c d e) (zip5 as bs cs ds es)

-- | Combine six sequences using the given function, analogous to
-- 'zipWith'.
--
zipWith6
    :: (Arrays a, Arrays b, Arrays c, Arrays d, Arrays e, Arrays f, Arrays g)
    => (Acc a -> Acc b -> Acc c -> Acc d -> Acc e -> Acc f -> Acc g)
    -> Seq [a]
    -> Seq [b]
    -> Seq [c]
    -> Seq [d]
    -> Seq [e]
    -> Seq [f]
    -> Seq [g]
zipWith6 op as bs cs ds es fs =
  map (\(T6 a b c d e f) -> op a b c d e f) (zip6 as bs cs ds es fs)

-- | Combine seven sequences using the given function, analogous to
-- 'zipWith'.
--
zipWith7
    :: (Arrays a, Arrays b, Arrays c, Arrays d, Arrays e, Arrays f, Arrays g, Arrays h)
    => (Acc a -> Acc b -> Acc c -> Acc d -> Acc e -> Acc f -> Acc g -> Acc h)
    -> Seq [a]
    -> Seq [b]
    -> Seq [c]
    -> Seq [d]
    -> Seq [e]
    -> Seq [f]
    -> Seq [g]
    -> Seq [h]
zipWith7 op as bs cs ds es fs gs =
  map (\(T7 a b c d e f g) -> op a b c d e f g) (zip7 as bs cs ds es fs gs)

-- | Combine eight sequences using the given function, analogous to
-- 'zipWith'.
--
zipWith8
    :: (Arrays a, Arrays b, Arrays c, Arrays d, Arrays e, Arrays f, Arrays g, Arrays h, Arrays i)
    => (Acc a -> Acc b -> Acc c -> Acc d -> Acc e -> Acc f -> Acc g -> Acc h -> Acc i)
    -> Seq [a]
    -> Seq [b]
    -> Seq [c]
    -> Seq [d]
    -> Seq [e]
    -> Seq [f]
    -> Seq [g]
    -> Seq [h]
    -> Seq [i]
zipWith8 op as bs cs ds es fs gs hs =
  map (\(T8 a b c d e f g h) -> op a b c d e f g h) (zip8 as bs cs ds es fs gs hs)

-- | Combine nine sequences using the given function, analogous to
-- 'zipWith'.
--
zipWith9
    :: (Arrays a, Arrays b, Arrays c, Arrays d, Arrays e, Arrays f, Arrays g, Arrays h, Arrays i, Arrays j)
    => (Acc a -> Acc b -> Acc c -> Acc d -> Acc e -> Acc f -> Acc g -> Acc h -> Acc i -> Acc j)
    -> Seq [a]
    -> Seq [b]
    -> Seq [c]
    -> Seq [d]
    -> Seq [e]
    -> Seq [f]
    -> Seq [g]
    -> Seq [h]
    -> Seq [i]
    -> Seq [j]
zipWith9 op as bs cs ds es fs gs hs is =
  map (\(T9 a b c d e f g h i) -> op a b c d e f g h i) (zip9 as bs cs ds es fs gs hs is)


-- | Combine the elements of two sequences
--
zip :: (Arrays a, Arrays b) => Seq [a] -> Seq [b] -> Seq [(a,b)]
zip = zipWith (curry lift)

-- | Take three streams and return a stream of triples, analogous to 'zip'.
--
zip3 :: (Arrays a, Arrays b, Arrays c)
     => Seq [a]
     -> Seq [b]
     -> Seq [c]
     -> Seq [(a,b,c)]
zip3 as bs cs =
  zipWith (\(T2 a b) c -> T3 a b c) (zip as bs) cs

-- | Take four streams and return a stream of quadruples, analogous to
-- 'zip'.
--
zip4 :: (Arrays a, Arrays b, Arrays c, Arrays d)
     => Seq [a]
     -> Seq [b]
     -> Seq [c]
     -> Seq [d]
     -> Seq [(a,b,c,d)]
zip4 as bs cs ds =
  zipWith (\(T2 a b) (T2 c d) -> T4 a b c d) (zip as bs) (zip cs ds)

-- | Take five streams and return a stream of five-tuples, analogous to
-- 'zip'.
--
zip5 :: (Arrays a, Arrays b, Arrays c, Arrays d, Arrays e)
     => Seq [a]
     -> Seq [b]
     -> Seq [c]
     -> Seq [d]
     -> Seq [e]
     -> Seq [(a,b,c,d,e)]
zip5 as bs cs ds es =
  zipWith (\(T3 a b c) (T2 d e) -> T5 a b c d e) (zip3 as bs cs) (zip ds es)

-- | Take six streams and return a stream of six-tuples, analogous to
-- 'zip'.
--
zip6 :: (Arrays a, Arrays b, Arrays c, Arrays d, Arrays e, Arrays f)
     => Seq [a]
     -> Seq [b]
     -> Seq [c]
     -> Seq [d]
     -> Seq [e]
     -> Seq [f]
     -> Seq [(a,b,c,d,e,f)]
zip6 as bs cs ds es fs =
  zipWith (\(T3 a b c) (T3 d e f) -> T6 a b c d e f)
    (zip3 as bs cs)
    (zip3 ds es fs)

-- | Take seven streams and return a stream of seven-tuples, analogous to
-- 'zip'.
--
zip7 :: (Arrays a, Arrays b, Arrays c, Arrays d, Arrays e, Arrays f, Arrays g)
     => Seq [a]
     -> Seq [b]
     -> Seq [c]
     -> Seq [d]
     -> Seq [e]
     -> Seq [f]
     -> Seq [g]
     -> Seq [(a,b,c,d,e,f,g)]
zip7 as bs cs ds es fs gs =
  zipWith (\(T4 a b c d) (T3 e f g) -> T7 a b c d e f g)
    (zip4 as bs cs ds)
    (zip3 es fs gs)

-- | Take eight streams and return a stream of eight-tuples, analogous to
-- 'zip'.
--
zip8 :: (Arrays a, Arrays b, Arrays c, Arrays d, Arrays e, Arrays f, Arrays g, Arrays h)
     => Seq [a]
     -> Seq [b]
     -> Seq [c]
     -> Seq [d]
     -> Seq [e]
     -> Seq [f]
     -> Seq [g]
     -> Seq [h]
     -> Seq [(a,b,c,d,e,f,g,h)]
zip8 as bs cs ds es fs gs hs =
  zipWith (\(T4 a b c d) (T4 e f g h) -> T8 a b c d e f g h)
    (zip4 as bs cs ds)
    (zip4 es fs gs hs)

-- | Take nine streams and return a stream of nine-tuples, analogous to
-- 'zip'.
--
zip9 :: (Arrays a, Arrays b, Arrays c, Arrays d, Arrays e, Arrays f, Arrays g, Arrays h, Arrays i)
     => Seq [a]
     -> Seq [b]
     -> Seq [c]
     -> Seq [d]
     -> Seq [e]
     -> Seq [f]
     -> Seq [g]
     -> Seq [h]
     -> Seq [i]
     -> Seq [(a,b,c,d,e,f,g,h,i)]
zip9 as bs cs ds es fs gs hs is =
  zipWith (\(T5 a b c d e) (T4 f g h i) -> T9 a b c d e f g h i)
    (zip5 as bs cs ds es)
    (zip4 fs gs hs is)


-- | The inverse of 'zip'. Take a sequence of pairs and return a pair of
-- sequences.
--
-- NOTE: This implies that the input stream will be buffered until both of
-- the resulting streams are consumed.
--
unzip :: (Arrays a, Arrays b) => Seq [(a,b)] -> (Seq [a], Seq [b])
unzip s = (map afst s, map asnd s)

-- | The inverse of 'zip3'
--
unzip3 :: (Arrays a, Arrays b, Arrays c)
       => Seq [(a,b,c)]
       -> (Seq [a], Seq [b], Seq [c])
unzip3 ss =
  let get1 (T3 x _ _) = x
      get2 (T3 _ x _) = x
      get3 (T3 _ _ x) = x
  in
  (map get1 ss, map get2 ss, map get3 ss)

-- | The inverse of 'zip4'
--
unzip4 :: (Arrays a, Arrays b, Arrays c, Arrays d)
       => Seq [(a,b,c,d)]
       -> (Seq [a], Seq [b], Seq [c], Seq [d])
unzip4 ss =
  let get1 (T4 x _ _ _) = x
      get2 (T4 _ x _ _) = x
      get3 (T4 _ _ x _) = x
      get4 (T4 _ _ _ x) = x
  in
  (map get1 ss, map get2 ss, map get3 ss, map get4 ss)

-- | The inverse of 'zip5'
--
unzip5 :: (Arrays a, Arrays b, Arrays c, Arrays d, Arrays e)
       => Seq [(a,b,c,d,e)]
       -> (Seq [a], Seq [b], Seq [c], Seq [d], Seq [e])
unzip5 ss =
  let get1 (T5 x _ _ _ _) = x
      get2 (T5 _ x _ _ _) = x
      get3 (T5 _ _ x _ _) = x
      get4 (T5 _ _ _ x _) = x
      get5 (T5 _ _ _ _ x) = x
  in
  (map get1 ss, map get2 ss, map get3 ss, map get4 ss, map get5 ss)

-- | The inverse of 'zip6'
--
unzip6 :: (Arrays a, Arrays b, Arrays c, Arrays d, Arrays e, Arrays f)
       => Seq [(a,b,c,d,e,f)]
       -> (Seq [a], Seq [b], Seq [c], Seq [d], Seq [e], Seq [f])
unzip6 ss =
  let get1 (T6 x _ _ _ _ _) = x
      get2 (T6 _ x _ _ _ _) = x
      get3 (T6 _ _ x _ _ _) = x
      get4 (T6 _ _ _ x _ _) = x
      get5 (T6 _ _ _ _ x _) = x
      get6 (T6 _ _ _ _ _ x) = x
  in
  (map get1 ss, map get2 ss, map get3 ss, map get4 ss, map get5 ss, map get6 ss)

-- | The inverse of 'zip7'
--
unzip7 :: (Arrays a, Arrays b, Arrays c, Arrays d, Arrays e, Arrays f, Arrays g)
       => Seq [(a,b,c,d,e,f,g)]
       -> (Seq [a], Seq [b], Seq [c], Seq [d], Seq [e], Seq [f], Seq [g])
unzip7 ss =
  let get1 (T7 x _ _ _ _ _ _) = x
      get2 (T7 _ x _ _ _ _ _) = x
      get3 (T7 _ _ x _ _ _ _) = x
      get4 (T7 _ _ _ x _ _ _) = x
      get5 (T7 _ _ _ _ x _ _) = x
      get6 (T7 _ _ _ _ _ x _) = x
      get7 (T7 _ _ _ _ _ _ x) = x
  in
  (map get1 ss, map get2 ss, map get3 ss, map get4 ss, map get5 ss, map get6 ss, map get7 ss)

-- | The inverse of 'zip8'
--
unzip8 :: (Arrays a, Arrays b, Arrays c, Arrays d, Arrays e, Arrays f, Arrays g, Arrays h)
       => Seq [(a,b,c,d,e,f,g,h)]
       -> (Seq [a], Seq [b], Seq [c], Seq [d], Seq [e], Seq [f], Seq [g], Seq [h])
unzip8 ss =
  let get1 (T8 x _ _ _ _ _ _ _) = x
      get2 (T8 _ x _ _ _ _ _ _) = x
      get3 (T8 _ _ x _ _ _ _ _) = x
      get4 (T8 _ _ _ x _ _ _ _) = x
      get5 (T8 _ _ _ _ x _ _ _) = x
      get6 (T8 _ _ _ _ _ x _ _) = x
      get7 (T8 _ _ _ _ _ _ x _) = x
      get8 (T8 _ _ _ _ _ _ _ x) = x
  in
  (map get1 ss, map get2 ss, map get3 ss, map get4 ss, map get5 ss, map get6 ss, map get7 ss, map get8 ss)

-- | The inverse of 'zip9'
--
unzip9 :: (Arrays a, Arrays b, Arrays c, Arrays d, Arrays e, Arrays f, Arrays g, Arrays h, Arrays i)
       => Seq [(a,b,c,d,e,f,g,h,i)]
       -> (Seq [a], Seq [b], Seq [c], Seq [d], Seq [e], Seq [f], Seq [g], Seq [h], Seq [i])
unzip9 ss =
  let get1 (T9 x _ _ _ _ _ _ _ _) = x
      get2 (T9 _ x _ _ _ _ _ _ _) = x
      get3 (T9 _ _ x _ _ _ _ _ _) = x
      get4 (T9 _ _ _ x _ _ _ _ _) = x
      get5 (T9 _ _ _ _ x _ _ _ _) = x
      get6 (T9 _ _ _ _ _ x _ _ _) = x
      get7 (T9 _ _ _ _ _ _ x _ _) = x
      get8 (T9 _ _ _ _ _ _ _ x _) = x
      get9 (T9 _ _ _ _ _ _ _ _ x) = x
  in
  (map get1 ss, map get2 ss, map get3 ss, map get4 ss, map get5 ss, map get6 ss, map get7 ss, map get8 ss, map get9 ss)


{--
-- | A batched map.
--
-- XXX: @RCE should this be resurrected? What is it used for?
--
mapBatch
    :: (Arrays a, Arrays b, Arrays c, Arrays s)
    => (Acc s -> Acc a -> Acc b)
    -> (Acc s -> Acc (Regular b) -> Acc (s, Regular c))
    -> (Acc s -> Acc (Irregular b) -> Acc (s, Irregular c))
    -> Acc s
    -> Seq [a]
    -> Seq [(s,c)]
mapBatch = Seq $$$$$ MapBatch
--}

-- |
--
-- XXX: @RCE document this!!!
-- XXX: Add example
--
fold
    :: (Arrays a, Arrays b, Arrays s)
    => (Acc s -> Seq [a] -> Seq b)
    -> (Acc b -> Acc s)
    -> Acc s
    -> Seq [a]
    -> Seq s
fold = Seq $$$$ FoldBatch

{--
-- | Fold a sequence by combining each element using the given binary
-- operation f, which must be associative.
--
-- XXX: @RCE where is this useful? Example?
--
foldSeqE :: Elt a
         => (Exp a -> Exp a -> Exp a)
         -> Exp a
         -> Seq [Scalar a]
         -> Seq (Scalar a)
foldSeqE f z =
  foldBatch
    (\s as -> lift (s, elements as))
    (\(unatup2 -> (s,as)) -> fold f (the s) as)
    (unit z)
--}
{--
-- | foldSeqFlatten f a0 x seq. f must be semi-associative, with
-- vector append (++) as the companion operator:
--
--   forall b sh1 a1 sh2 a2.
--     f (f b sh1 a1) sh2 a2 = f b (sh1 ++ sh2) (a1 ++ a2).
--
-- It is common to ignore the shape vectors, yielding the usual
-- semi-associativity law:
--
--   f b a _ = b + a,
--
-- for some (+) satisfying:
--
--   forall b a1 a2. (b + a1) + a2 = b + (a1 ++ a2).
--
-- XXX: @RCE where is this useful? Example?
--
foldSeqFlatten
    :: (Arrays a, Shape sh, Elt e)
    => (Acc a -> Acc (Vector sh) -> Acc (Vector e) -> Acc a)
    -> Acc a
    -> Seq [Array sh e]
    -> Seq a
foldSeqFlatten f =
  foldBatch
    (\a s -> lift (a, shapes s, elements s))
    (uncurry3 f)
--}

{--
-- | Perform an exclusive left-to-right scan over a scalar sequence x by
-- combining each element using the given binary operation (+). (+) must be
-- associative.
--
-- XXX: @RCE should this be resurrected?
--
scanSeqE
   :: Elt e
   => (Exp e -> Exp e -> Exp e)
   -> Exp e
   -> Seq [Scalar e]
   -> Seq [Scalar e]
scanSeqE f z
  = mapSeq asnd
  . mapBatch
      (const id)
      (\acc es -> let (es', acc') = scanl' f (the acc) (flatten (unregular es))
                   in lift (acc', regular es'))
      (\acc es -> let (es', acc') = scanl' f (the acc) (irregularValues es)
                   in lift (acc', sparsify (regular es')))
      (unit z)
--}

-- | Concatenate the elements of all arrays in the input sequence to
-- produce a single flat vector.
--
-- XXX: Add example
--
elements :: (Shape sh, Elt e) => Seq [Array sh e] -> Seq (Vector e)
elements = Seq . Elements

-- | Produce a vector of the extents of the arrays of the sequence
--
-- XXX: Add example
--
shapes :: (Shape sh, Elt e) => Seq [Array sh e] -> Seq (Vector sh)
shapes = elements . map (unit . shape)

-- | Concatenate the elements of a sequence into a single array.
--
-- The extent of the resulting array is the length of the sequence as the
-- outer-most dimension, and the intersection of extents of the source
-- arrays as the inner dimensions.
--
-- XXX: Add example
--
tabulate :: (Shape sh, Elt e) => Seq [Array sh e] -> Seq (Array (sh:.Int) e)
tabulate = Seq . Tabulate

