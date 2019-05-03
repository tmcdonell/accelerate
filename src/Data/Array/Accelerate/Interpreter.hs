{-# LANGUAGE BangPatterns        #-}
{-# LANGUAGE CPP                 #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE FlexibleInstances   #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE MagicHash           #-}
{-# LANGUAGE PatternGuards       #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE RecordWildCards     #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell     #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE TypeFamilies        #-}
{-# LANGUAGE TypeOperators       #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE ViewPatterns        #-}
{-# OPTIONS_GHC -fno-warn-name-shadowing #-}
{-# OPTIONS_HADDOCK prune #-}
-- |
-- Module      : Data.Array.Accelerate.Interpreter
-- Copyright   : [2008..2019] The Accelerate Team
-- License     : BSD3
--
-- Maintainer  : Trevor L. McDonell <trevor.mcdonell@gmail.com>
-- Stability   : experimental
-- Portability : non-portable (GHC extensions)
--
-- This interpreter is meant to be a reference implementation of the semantics
-- of the embedded array language. The emphasis is on defining the semantics
-- clearly, not on performance.
--

-- [/Surface types versus representation types:/]
--
-- As a general rule, we perform all computations on representation types and we
-- store all data as values of representation types. To guarantee the type
-- safety of the interpreter, this currently implies a lot of conversions
-- between surface and representation types. Optimising the code by eliminating
-- back and forth conversions is fine, but only where it doesn't negatively
-- affects clarity---after all, the main purpose of the interpreter is to serve
-- as an executable specification.
--

module Data.Array.Accelerate.Interpreter (

  Smart.Acc, Arrays,
  Afunction, AfunctionR,

  -- * Interpret an array expression
  run, run1, runN,

  -- * Interpret a sequence expression
  streamOut,

  -- Internal (hidden)
  evalPrj,
  evalPrim, evalPrimConst, evalUndef, evalCoerce,

) where

-- standard libraries
import Control.DeepSeq
import Control.Exception
import Control.Monad
import Control.Monad.ST
import Data.Bits
import Data.Char                                                    ( chr, ord )
import Data.Maybe                                                   ( fromMaybe, fromJust )
import Data.Primitive.ByteArray
import Data.Primitive.Types
import Data.Typeable
import System.IO.Unsafe                                             ( unsafePerformIO )
import Text.Printf                                                  ( printf )
import Unsafe.Coerce
import Prelude                                                      hiding ( sum )

-- friends
import Data.Array.Accelerate.AST                                    hiding ( Boundary, PreBoundary(..) )
import Data.Array.Accelerate.Analysis.Match
import Data.Array.Accelerate.Analysis.Type                          ( sizeOfScalarType, sizeOfSingleType )
import Data.Array.Accelerate.Array.Data
import Data.Array.Accelerate.Array.Lifted                           ( divide )
import Data.Array.Accelerate.Array.Representation                   ( SliceIndex(..) )
import Data.Array.Accelerate.Array.Sugar
import Data.Array.Accelerate.Error
import Data.Array.Accelerate.Product
import Data.Array.Accelerate.Trafo                                  hiding ( Delayed )
import Data.Array.Accelerate.Trafo.Base                             ( DelayedSeq, StreamSeq(..), Extend(..) )
import Data.Array.Accelerate.Type
import qualified Data.Array.Accelerate.AST                          as AST
import qualified Data.Array.Accelerate.Array.Representation         as R
import qualified Data.Array.Accelerate.Smart                        as Smart
import qualified Data.Array.Accelerate.Trafo                        as AST

import qualified Data.Array.Accelerate.Debug                        as D


-- Program execution
-- -----------------

-- | Run a complete embedded array program using the reference interpreter.
--
run :: Arrays a => Smart.Acc a -> a
run a = unsafePerformIO execute
  where
    !acc    = convertAccWith config a
    execute = do
      D.dumpGraph $!! acc
      D.dumpSimplStats
      phase "execute" D.elapsed (evaluate (evalOpenAcc acc Empty))

-- | This is 'runN' specialised to an array program of one argument.
--
run1 :: (Arrays a, Arrays b) => (Smart.Acc a -> Smart.Acc b) -> a -> b
run1 = runN

-- | Prepare and execute an embedded array program.
--
runN :: Afunction f => f -> AfunctionR f
runN f = go
  where
    !acc    = convertAfunWith config f
    !afun   = unsafePerformIO $ do
                D.dumpGraph $!! acc
                D.dumpSimplStats
                return acc
    !go     = eval afun Empty
    --
    eval :: DelayedOpenAfun aenv f -> Val aenv -> f
    eval (Alam f)  aenv = \a -> eval f (aenv `Push` a)
    eval (Abody b) aenv = unsafePerformIO $ phase "execute" D.elapsed (evaluate (evalOpenAcc b aenv))


-- | Stream a lazily read list of input arrays through the given program,
-- collecting results as we go
--
streamOut :: Arrays a => Smart.Seq [a] -> [a]
streamOut seq = let seq' = convertSeqWith config seq
                in evalDelayedSeq seq'


config :: Phase
config =  Phase
  { recoverAccSharing      = True
  , recoverExpSharing      = True
  , recoverSeqSharing      = True
  , floatOutAccFromExp     = True
  , enableAccFusion        = True
  , convertOffsetOfSegment = False
  , convertSubarrayToIndex = False
  , vectoriseSequences     = True
  }

-- Debugging
-- ---------

phase :: String -> (Double -> Double -> String) -> IO a -> IO a
phase n fmt go = D.timed D.dump_phases (\wall cpu -> printf "phase %s: %s" n (fmt wall cpu)) go


-- Delayed Arrays
-- --------------

-- Note that in contrast to the representation used in the optimised AST, the
-- delayed array representation used here is _only_ for delayed arrays --- we do
-- not require an optional Manifest|Delayed data type to evaluate the program.
--
data Delayed a where
  Delayed :: sh
          -> (sh -> e)
          -> (Int -> e)
          -> Delayed (Array sh e)


-- Array expression evaluation
-- ---------------------------

type EvalAcc acc = forall aenv a. acc aenv a -> Val aenv -> a

-- Evaluate an open array function
--
evalOpenAfun :: DelayedOpenAfun aenv f -> Val aenv -> f
evalOpenAfun (Alam  f) aenv = \a -> evalOpenAfun f (aenv `Push` a)
evalOpenAfun (Abody b) aenv = evalOpenAcc b aenv


-- The core interpreter for optimised array programs
--
evalOpenAcc
    :: forall aenv a.
       DelayedOpenAcc aenv a
    -> Val aenv
    -> a
evalOpenAcc AST.Delayed{}       _    = $internalError "evalOpenAcc" "expected manifest array"
evalOpenAcc (AST.Manifest pacc) aenv =
  let
      manifest :: forall a'. Arrays a' => DelayedOpenAcc aenv a' -> a'
      manifest acc =
        let a' = evalOpenAcc acc aenv
        in  rnfArrays (arrays @a') (fromArr a') `seq` a'

      delayed :: DelayedOpenAcc aenv (Array sh e) -> Delayed (Array sh e)
      delayed AST.Manifest{}  = $internalError "evalOpenAcc" "expected delayed array"
      delayed AST.Delayed{..} = Delayed (evalE extentD) (evalF indexD) (evalF linearIndexD)

      evalE :: DelayedExp aenv t -> t
      evalE exp = evalPreExp evalOpenAcc exp aenv

      evalF :: DelayedFun aenv f -> f
      evalF fun = evalPreFun evalOpenAcc fun aenv

      evalB :: AST.PreBoundary DelayedOpenAcc aenv t -> Boundary t
      evalB bnd = evalPreBoundary evalOpenAcc bnd aenv
  in
  case pacc of
    Avar ix                     -> prj ix aenv
    Alet acc1 acc2              -> evalOpenAcc acc2 (aenv `Push` manifest acc1)
    Atuple atup                 -> toAtuple $ evalAtuple atup aenv
    Aprj ix atup                -> evalPrj ix . fromAtuple $ manifest atup
    Apply afun acc              -> evalOpenAfun afun aenv  $ manifest acc
    Aforeign _ afun acc         -> evalOpenAfun afun Empty $ manifest acc
    Acond p acc1 acc2
      | evalE p                 -> manifest acc1
      | otherwise               -> manifest acc2

    Awhile cond body acc        -> go (manifest acc)
      where
        p       = evalOpenAfun cond aenv
        f       = evalOpenAfun body aenv
        go !x
          | p x ! Z     = go (f x)
          | otherwise   = x

    Use arr                     -> toArr arr
    Subarray ix sh arr          -> subarrayOp (evalE ix) (evalE sh) arr
    Unit e                      -> unitOp (evalE e)
    Collect min max i s         -> evalSeq (evalE min) (evalE <$> max) (evalE <$> i) s aenv


    -- Producers
    -- ---------
    Map f acc                   -> mapOp (evalF f) (delayed acc)
    Generate sh f               -> generateOp (evalE sh) (evalF f)
    Transform sh p f acc        -> transformOp (evalE sh) (evalF p) (evalF f) (delayed acc)
    Backpermute sh p acc        -> backpermuteOp (evalE sh) (evalF p) (delayed acc)
    Reshape sh acc              -> reshapeOp (evalE sh) (manifest acc)

    ZipWith f acc1 acc2         -> zipWithOp (evalF f) (delayed acc1) (delayed acc2)
    Replicate slice slix acc    -> replicateOp slice (evalE slix) (manifest acc)
    Slice slice acc slix        -> sliceOp slice (manifest acc) (evalE slix)

    -- Consumers
    -- ---------
    Fold f z acc                -> foldOp (evalF f) (evalE z) (delayed acc)
    Fold1 f acc                 -> fold1Op (evalF f) (delayed acc)
    FoldSeg f z acc seg         -> foldSegOp (evalF f) (evalE z) (delayed acc) (delayed seg)
    Fold1Seg f acc seg          -> fold1SegOp (evalF f) (delayed acc) (delayed seg)
    Scanl f z acc               -> scanlOp (evalF f) (evalE z) (delayed acc)
    Scanl' f z acc              -> scanl'Op (evalF f) (evalE z) (delayed acc)
    Scanl1 f acc                -> scanl1Op (evalF f) (delayed acc)
    Scanr f z acc               -> scanrOp (evalF f) (evalE z) (delayed acc)
    Scanr' f z acc              -> scanr'Op (evalF f) (evalE z) (delayed acc)
    Scanr1 f acc                -> scanr1Op (evalF f) (delayed acc)
    Permute f def p acc         -> permuteOp (evalF f) (manifest def) (evalF p) (delayed acc)
    Stencil sten b acc          -> stencilOp (evalF sten) (evalB b) (delayed acc)
    Stencil2 sten b1 a1 b2 a2   -> stencil2Op (evalF sten) (evalB b1) (delayed a1) (evalB b2) (delayed a2)

-- Array tuple construction and projection
--
evalAtuple :: Atuple (DelayedOpenAcc aenv) t -> Val aenv -> t
evalAtuple NilAtup        _    = ()
evalAtuple (SnocAtup t a) aenv = (evalAtuple t aenv, evalOpenAcc a aenv)


-- Array primitives
-- ----------------

unitOp :: Elt e => e -> Scalar e
unitOp e = fromFunction Z (const e)


generateOp
    :: (Shape sh, Elt e)
    => sh
    -> (sh -> e)
    -> Array sh e
generateOp = fromFunction


transformOp
    :: (Shape sh', Elt b)
    => sh'
    -> (sh' -> sh)
    -> (a -> b)
    -> Delayed (Array sh a)
    -> Array sh' b
transformOp sh' p f (Delayed _ xs _)
  = fromFunction sh' (\ix -> f (xs $ p ix))


reshapeOp
    :: (Shape sh, Shape sh')
    => sh
    -> Array sh' e
    -> Array sh  e
reshapeOp newShape arr@(Array _ adata)
  = $boundsCheck "reshape" "shape mismatch" (size newShape == size (shape arr))
  $ Array (fromElt newShape) adata


replicateOp
    :: (Shape sh, Shape sl, Elt slix, Elt e)
    => SliceIndex (EltRepr slix) (EltRepr sl) co (EltRepr sh)
    -> slix
    -> Array sl e
    -> Array sh e
replicateOp slice slix arr
  = fromFunction (toElt sh) (\ix -> arr ! liftToElt pf ix)
  where
    (sh, pf) = extend slice (fromElt slix) (fromElt (shape arr))

    extend :: SliceIndex slix sl co dim
           -> slix
           -> sl
           -> (dim, dim -> sl)
    extend SliceNil              ()        ()
      = ((), const ())
    extend (SliceAll sliceIdx)   (slx, ()) (sl, sz)
      = let (dim', f') = extend sliceIdx slx sl
        in  ((dim', sz), \(ix, i) -> (f' ix, i))
    extend (SliceFixed sliceIdx) (slx, sz) sl
      = let (dim', f') = extend sliceIdx slx sl
        in  ((dim', sz), \(ix, _) -> f' ix)


sliceOp
    :: (Shape sh, Shape sl, Elt slix, Elt e)
    => SliceIndex (EltRepr slix) (EltRepr sl) co (EltRepr sh)
    -> Array sh e
    -> slix
    -> Array sl e
sliceOp slice arr slix
  = fromFunction (toElt sh') (\ix -> arr ! liftToElt pf ix)
  where
    (sh', pf) = restrict slice (fromElt slix) (fromElt (shape arr))

    restrict :: SliceIndex slix sl co sh
             -> slix
             -> sh
             -> (sl, sl -> sh)
    restrict SliceNil              ()        ()
      = ((), const ())
    restrict (SliceAll sliceIdx)   (slx, ()) (sl, sz)
      = let (sl', f') = restrict sliceIdx slx sl
        in  ((sl', sz), \(ix, i) -> (f' ix, i))
    restrict (SliceFixed sliceIdx) (slx, i)  (sl, sz)
      = let (sl', f') = restrict sliceIdx slx sl
        in  $indexCheck "slice" i sz $ (sl', \ix -> (f' ix, i))


mapOp :: (Shape sh, Elt b)
      => (a -> b)
      -> Delayed (Array sh a)
      -> Array sh b
mapOp f (Delayed sh xs _)
  = fromFunction sh (\ix -> f (xs ix))


zipWithOp
    :: (Shape sh, Elt c)
    => (a -> b -> c)
    -> Delayed (Array sh a)
    -> Delayed (Array sh b)
    -> Array sh c
zipWithOp f (Delayed shx xs _) (Delayed shy ys _)
  = fromFunction (shx `intersect` shy) (\ix -> f (xs ix) (ys ix))

-- zipWith'Op
--     :: (Shape sh, Elt a)
--     => (a -> a -> a)
--     -> Delayed (Array sh a)
--     -> Delayed (Array sh a)
--     -> Array sh a
-- zipWith'Op f (Delayed shx xs _) (Delayed shy ys _)
--   = fromFunction (shx `union` shy) (\ix -> if ix `outside` shx
--                                            then ys ix
--                                            else if ix `outside` shy
--                                            then xs ix
--                                            else f (xs ix) (ys ix))
--   where
--     a `outside` b = or $ zipWith (>=) (shapeToList a) (shapeToList b)


foldOp
    :: (Shape sh, Elt e)
    => (e -> e -> e)
    -> e
    -> Delayed (Array (sh :. Int) e)
    -> Array sh e
foldOp f z (Delayed (sh :. n) arr _)
  = fromFunction sh (\ix -> iter (Z:.n) (\(Z:.i) -> arr (ix :. i)) f z)


fold1Op
    :: (Shape sh, Elt e)
    => (e -> e -> e)
    -> Delayed (Array (sh :. Int) e)
    -> Array sh e
fold1Op f (Delayed (sh :. n) arr _)
  = $boundsCheck "fold1" "empty array" (n > 0)
  $ fromFunction sh (\ix -> iter1 (Z:.n) (\(Z:.i) -> arr (ix :. i)) f)


foldSegOp
    :: forall sh e i. (Shape sh, Elt e, Elt i, IsIntegral i)
    => (e -> e -> e)
    -> e
    -> Delayed (Array (sh :. Int) e)
    -> Delayed (Segments i)
    -> Array (sh :. Int) e
foldSegOp f z (Delayed (sh :. _) arr _) seg@(Delayed (Z :. n) _ _)
  | IntegralDict <- integralDict (integralType :: IntegralType i)
  = fromFunction (sh :. n)
  $ \(sz :. ix) -> let start = fromIntegral $ offset ! (Z :. ix)
                       end   = fromIntegral $ offset ! (Z :. ix+1)
                   in
                   iter (Z :. end-start) (\(Z:.i) -> arr (sz :. start+i)) f z
  where
    offset      = scanlOp (+) 0 seg


fold1SegOp
    :: forall sh e i. (Shape sh, Elt e, Elt i, IsIntegral i)
    => (e -> e -> e)
    -> Delayed (Array (sh :. Int) e)
    -> Delayed (Segments i)
    -> Array (sh :. Int) e
fold1SegOp f (Delayed (sh :. _) arr _) seg@(Delayed (Z :. n) _ _)
  | IntegralDict <- integralDict (integralType :: IntegralType i)
  = fromFunction (sh :. n)
  $ \(sz :. ix) -> let start = fromIntegral $ offset ! (Z :. ix)
                       end   = fromIntegral $ offset ! (Z :. ix+1)
                   in
                   $boundsCheck "fold1Seg" "empty segment" (end > start)
                   $ iter1 (Z :. end-start) (\(Z:.i) -> arr (sz :. start+i)) f
  where
    offset      = scanlOp (+) 0 seg


scanl1Op
    :: (Shape sh, Elt e)
    => (e -> e -> e)
    -> Delayed (Array (sh:.Int) e)
    -> Array (sh:.Int) e
scanl1Op f (Delayed sh@(_ :. n) ain _)
  = $boundsCheck "scanl1" "empty array" (n > 0)
  $ adata `seq` Array (fromElt sh) adata
  where
    f'          = sinkFromElt2 f
    --
    (adata, _)  = runArrayData $ do
      aout <- newArrayData (size sh)

      let write (sz:.0) = unsafeWriteArrayData aout (toIndex sh (sz:.0)) (fromElt (ain (sz:.0)))
          write (sz:.i) = do
            x <- unsafeReadArrayData aout (toIndex sh (sz:.i-1))
            y <- return $ fromElt (ain (sz:.i))
            unsafeWriteArrayData aout (toIndex sh (sz:.i)) (f' x y)

      iter sh write (>>) (return ())
      return (aout, undefined)


scanlOp
    :: (Shape sh, Elt e)
    => (e -> e -> e)
    -> e
    -> Delayed (Array (sh:.Int) e)
    -> Array (sh:.Int) e
scanlOp f z (Delayed (sh :. n) ain _)
  = adata `seq` Array (fromElt sh') adata
  where
    sh'         = sh :. n+1
    f'          = sinkFromElt2 f
    --
    (adata, _)  = runArrayData $ do
      aout <- newArrayData (size sh')

      let write (sz:.0) = unsafeWriteArrayData aout (toIndex sh' (sz:.0)) (fromElt z)
          write (sz:.i) = do
            x <- unsafeReadArrayData aout (toIndex sh' (sz:.i-1))
            y <- return $ fromElt (ain (sz:.i-1))
            unsafeWriteArrayData aout (toIndex sh' (sz:.i)) (f' x y)

      iter sh' write (>>) (return ())
      return (aout, undefined)


scanl'Op
    :: (Shape sh, Elt e)
    => (e -> e -> e)
    -> e
    -> Delayed (Array (sh:.Int) e)
    -> (Array (sh:.Int) e, Array sh e)
scanl'Op f z (Delayed (sh :. n) ain _)
  = aout `seq` asum `seq` ( Array (fromElt (sh:.n)) aout
                          , Array (fromElt sh)      asum )
  where
    f'          = sinkFromElt2 f
    --
    (AD_Pair aout asum, _) = runArrayData $ do
      aout <- newArrayData (size (sh:.n))
      asum <- newArrayData (size sh)

      let write (sz:.0)
            | n == 0    = unsafeWriteArrayData asum (toIndex sh sz) (fromElt z)
            | otherwise = unsafeWriteArrayData aout (toIndex (sh:.n) (sz:.0)) (fromElt z)
          write (sz:.i) = do
            x <- unsafeReadArrayData aout (toIndex (sh:.n) (sz:.i-1))
            y <- return $ fromElt (ain (sz:.i-1))
            if i == n
              then unsafeWriteArrayData asum (toIndex sh      sz)      (f' x y)
              else unsafeWriteArrayData aout (toIndex (sh:.n) (sz:.i)) (f' x y)

      iter (sh:.n+1) write (>>) (return ())
      return (AD_Pair aout asum, undefined)


scanrOp
    :: (Shape sh, Elt e)
    => (e -> e -> e)
    -> e
    -> Delayed (Array (sh:.Int) e)
    -> Array (sh:.Int) e
scanrOp f z (Delayed (sz :. n) ain _)
  = adata `seq` Array (fromElt sh') adata
  where
    sh'         = sz :. n+1
    f'          = sinkFromElt2 f
    --
    (adata, _)  = runArrayData $ do
      aout <- newArrayData (size sh')

      let write (sz:.0) = unsafeWriteArrayData aout (toIndex sh' (sz:.n)) (fromElt z)
          write (sz:.i) = do
            x <- return $ fromElt (ain (sz:.n-i))
            y <- unsafeReadArrayData aout (toIndex sh' (sz:.n-i+1))
            unsafeWriteArrayData aout (toIndex sh' (sz:.n-i)) (f' x y)

      iter sh' write (>>) (return ())
      return (aout, undefined)


scanr1Op
    :: (Shape sh, Elt e)
    => (e -> e -> e)
    -> Delayed (Array (sh:.Int) e)
    -> Array (sh:.Int) e
scanr1Op f (Delayed sh@(_ :. n) ain _)
  = $boundsCheck "scanr1" "empty array" (n > 0)
  $ adata `seq` Array (fromElt sh) adata
  where
    f'          = sinkFromElt2 f
    --
    (adata, _)  = runArrayData $ do
      aout <- newArrayData (size sh)

      let write (sz:.0) = unsafeWriteArrayData aout (toIndex sh (sz:.n-1)) (fromElt (ain (sz:.n-1)))
          write (sz:.i) = do
            x <- return $ fromElt (ain (sz:.n-i-1))
            y <- unsafeReadArrayData aout (toIndex sh (sz:.n-i))
            unsafeWriteArrayData aout (toIndex sh (sz:.n-i-1)) (f' x y)

      iter sh write (>>) (return ())
      return (aout, undefined)


scanr'Op
    :: forall sh e. (Shape sh, Elt e)
    => (e -> e -> e)
    -> e
    -> Delayed (Array (sh:.Int) e)
    -> (Array (sh:.Int) e, Array sh e)
scanr'Op f z (Delayed (sh :. n) ain _)
  = aout `seq` asum `seq` ( Array (fromElt (sh:.n)) aout
                          , Array (fromElt sh)      asum )
  where
    f'          = sinkFromElt2 f
    --
    (AD_Pair aout asum, _) = runArrayData $ do
      aout <- newArrayData (size (sh:.n))
      asum <- newArrayData (size sh)

      let write (sz:.0)
            | n == 0    = unsafeWriteArrayData asum (toIndex sh sz) (fromElt z)
            | otherwise = unsafeWriteArrayData aout (toIndex (sh:.n) (sz:.n-1)) (fromElt z)

          write (sz:.i) = do
            x <- return $ fromElt (ain (sz:.n-i))
            y <- unsafeReadArrayData aout (toIndex (sh:.n) (sz:.n-i))
            if i == n
              then unsafeWriteArrayData asum (toIndex sh      sz)          (f' x y)
              else unsafeWriteArrayData aout (toIndex (sh:.n) (sz:.n-i-1)) (f' x y)

      iter (sh:.n+1) write (>>) (return ())
      return (AD_Pair aout asum, undefined)


permuteOp
    :: (Shape sh, Shape sh', Elt e)
    => (e -> e -> e)
    -> Array sh' e
    -> (sh -> sh')
    -> Delayed (Array sh  e)
    -> Array sh' e
permuteOp f def@(Array _ adef) p (Delayed sh _ ain)
  = adata `seq` Array (fromElt sh') adata
  where
    sh'         = shape def
    n'          = size sh'
    f'          = sinkFromElt2 f
    --
    (adata, _)  = runArrayData $ do
      aout <- newArrayData n'

      let -- initialise array with default values
          init i
            | i >= n'   = return ()
            | otherwise = do
                x <- unsafeReadArrayData adef i
                unsafeWriteArrayData aout i x
                init (i+1)

          -- project each element onto the destination array and update
          update src
            = let dst   = p src
                  i     = toIndex sh  src
                  j     = toIndex sh' dst
              in
              unless (fromElt dst == R.ignore) $ do
                x <- return . fromElt $  ain  i
                y <- unsafeReadArrayData aout j
                unsafeWriteArrayData aout j (f' x y)

      init 0
      iter sh update (>>) (return ())
      return (aout, undefined)


backpermuteOp
    :: (Shape sh', Elt e)
    => sh'
    -> (sh' -> sh)
    -> Delayed (Array sh e)
    -> Array sh' e
backpermuteOp sh' p (Delayed _ arr _)
  = fromFunction sh' (\ix -> arr $ p ix)

subarrayOp
    :: (Shape sh, Elt e)
    => sh
    -> sh
    -> Array sh e
    -> Array sh e
subarrayOp ix sh arr
  = fromFunction sh (\ix' -> arr ! (ix `offset` ix'))


stencilOp
    :: (Stencil sh a stencil, Elt b)
    => (stencil -> b)
    -> Boundary (Array sh a)
    -> Delayed  (Array sh a)
    -> Array sh b
stencilOp stencil bnd arr@(Delayed sh _ _)
  = fromFunction sh
  $ stencil . stencilAccess (bounded bnd arr)


stencil2Op
    :: (Stencil sh a stencil1, Stencil sh b stencil2, Elt c)
    => (stencil1 -> stencil2 -> c)
    -> Boundary (Array sh a)
    -> Delayed  (Array sh a)
    -> Boundary (Array sh b)
    -> Delayed  (Array sh b)
    -> Array sh c
stencil2Op stencil bnd1 arr1@(Delayed sh1 _ _) bnd2 arr2@(Delayed sh2 _ _)
  = fromFunction (sh1 `intersect` sh2) f
  where
    f ix  = stencil (stencilAccess (bounded bnd1 arr1) ix)
                    (stencilAccess (bounded bnd2 arr2) ix)

stencilAccess
    :: Stencil sh e stencil
    => (sh -> e)
    -> sh
    -> stencil
stencilAccess = goR stencil
  where
    -- Base cases, nothing interesting to do here since we know the lower
    -- dimension is Z.
    --
    goR :: StencilR sh e stencil -> (sh -> e) -> sh -> stencil
    goR StencilRunit3 rf ix =
      let
          z :. i = ix
          rf' d  = rf (z :. i+d)
      in
      ( rf' (-1)
      , rf'   0
      , rf'   1
      )

    goR StencilRunit5 rf ix =
      let z :. i = ix
          rf' d  = rf (z :. i+d)
      in
      ( rf' (-2)
      , rf' (-1)
      , rf'   0
      , rf'   1
      , rf'   2
      )

    goR StencilRunit7 rf ix =
      let z :. i = ix
          rf' d  = rf (z :. i+d)
      in
      ( rf' (-3)
      , rf' (-2)
      , rf' (-1)
      , rf'   0
      , rf'   1
      , rf'   2
      , rf'   3
      )

    goR StencilRunit9 rf ix =
      let z :. i = ix
          rf' d  = rf (z :. i+d)
      in
      ( rf' (-4)
      , rf' (-3)
      , rf' (-2)
      , rf' (-1)
      , rf'   0
      , rf'   1
      , rf'   2
      , rf'   3
      , rf'   4
      )

    -- Recursive cases. Note that because the stencil pattern is defined with
    -- cons ordering, whereas shapes (and indices) are defined as a snoc-list,
    -- when we recurse on the stencil structure we must manipulate the
    -- _left-most_ index component.
    --
    goR (StencilRtup3 s1 s2 s3) rf ix =
      let (i, ix') = uncons ix
          rf' d ds = rf (cons (i+d) ds)
      in
      ( goR s1 (rf' (-1)) ix'
      , goR s2 (rf'   0)  ix'
      , goR s3 (rf'   1)  ix'
      )

    goR (StencilRtup5 s1 s2 s3 s4 s5) rf ix =
      let (i, ix') = uncons ix
          rf' d ds = rf (cons (i+d) ds)
      in
      ( goR s1 (rf' (-2)) ix'
      , goR s2 (rf' (-1)) ix'
      , goR s3 (rf'   0)  ix'
      , goR s4 (rf'   1)  ix'
      , goR s5 (rf'   2)  ix'
      )

    goR (StencilRtup7 s1 s2 s3 s4 s5 s6 s7) rf ix =
      let (i, ix') = uncons ix
          rf' d ds = rf (cons (i+d) ds)
      in
      ( goR s1 (rf' (-3)) ix'
      , goR s2 (rf' (-2)) ix'
      , goR s3 (rf' (-1)) ix'
      , goR s4 (rf'   0)  ix'
      , goR s5 (rf'   1)  ix'
      , goR s6 (rf'   2)  ix'
      , goR s7 (rf'   3)  ix'
      )

    goR (StencilRtup9 s1 s2 s3 s4 s5 s6 s7 s8 s9) rf ix =
      let (i, ix') = uncons ix
          rf' d ds = rf (cons (i+d) ds)
      in
      ( goR s1 (rf' (-4)) ix'
      , goR s2 (rf' (-3)) ix'
      , goR s3 (rf' (-2)) ix'
      , goR s4 (rf' (-1)) ix'
      , goR s5 (rf'   0)  ix'
      , goR s6 (rf'   1)  ix'
      , goR s7 (rf'   2)  ix'
      , goR s8 (rf'   3)  ix'
      , goR s9 (rf'   4)  ix'
      )

    -- Add a left-most component to an index
    --
    cons :: forall sh. Shape sh => Int -> sh -> (sh :. Int)
    cons ix extent = toElt $ go (eltType @sh) (fromElt extent)
      where
        go :: TupleType t -> t -> (t, Int)
        go TypeRunit         ()       = ((), ix)
        go (TypeRpair th tz) (sh, sz)
          | TypeRscalar t <- tz
          , Just Refl     <- matchScalarType t (scalarType :: ScalarType Int)
          = (go th sh, sz)
        go _ _
          = $internalError "cons" "expected index with Int components"

    -- Remove the left-most index of an index, and return the remainder
    --
    uncons :: forall sh. Shape sh => sh :. Int -> (Int, sh)
    uncons extent = let (i,ix) = go (eltType @(sh:.Int)) (fromElt extent)
                    in  (i, toElt ix)
      where
        go :: TupleType (t, Int) -> (t, Int) -> (Int, t)
        go (TypeRpair TypeRunit _)           ((), v) = (v, ())
        go (TypeRpair t1@(TypeRpair _ t2) _) (v1,v3)
          | TypeRscalar t <- t2
          , Just Refl     <- matchScalarType t (scalarType :: ScalarType Int)
          = let (i, v1') = go t1 v1
            in  (i, (v1', v3))
        go _ _
          = $internalError "uncons" "expected index with Int components"


bounded
    :: (Shape sh, Elt e)
    => Boundary (Array sh e)
    -> Delayed (Array sh e)
    -> sh
    -> e
bounded bnd (Delayed sh f _) ix =
  if inside sh ix
    then f ix
    else
      case bnd of
        Function g -> g ix
        Constant v -> toElt v
        _          -> f (bound sh ix)

  where
    -- Whether the index (second argument) is inside the bounds of the given
    -- shape (first argument).
    --
    inside :: forall sh. Shape sh => sh -> sh -> Bool
    inside sh1 ix1 = go (eltType @sh) (fromElt sh1) (fromElt ix1)
      where
        go :: TupleType t -> t -> t -> Bool
        go TypeRunit          ()       ()      = True
        go (TypeRpair tsh ti) (sh, sz) (ih,iz)
          = if go ti sz iz
              then go tsh sh ih
              else False
        go (TypeRscalar t) sz iz
          | Just Refl <- matchScalarType t (scalarType :: ScalarType Int)
          = if iz < 0 || iz >= sz
              then False
              else True
          --
          | otherwise
          = $internalError "inside" "expected index with Int components"

    -- Return the index (second argument), updated to obey the given boundary
    -- conditions when outside the bounds of the given shape (first argument)
    --
    bound :: forall sh. Shape sh => sh -> sh -> sh
    bound sh1 ix1 = toElt $ go (eltType @sh) (fromElt sh1) (fromElt ix1)
      where
        go :: TupleType t -> t -> t -> t
        go TypeRunit          ()       ()       = ()
        go (TypeRpair tsh ti) (sh, sz) (ih, iz) = (go tsh sh ih, go ti sz iz)
        go (TypeRscalar t)    sz       iz
          | Just Refl <- matchScalarType t (scalarType :: ScalarType Int)
          = let i | iz < 0    = case bnd of
                                  Clamp  -> 0
                                  Mirror -> -iz
                                  Wrap   -> sz + iz
                                  _      -> $internalError "bound" "unexpected boundary condition"
                  | iz >= sz  = case bnd of
                                  Clamp  -> sz - 1
                                  Mirror -> sz - (iz - sz + 2)
                                  Wrap   -> iz - sz
                                  _      -> $internalError "bound" "unexpected boundary condition"
                  | otherwise = iz
            in i
          | otherwise
          = $internalError "bound" "expected index with Int components"


-- Stencil boundary conditions
-- ---------------------------

data Boundary t where
  Clamp    :: Boundary t
  Mirror   :: Boundary t
  Wrap     :: Boundary t
  Constant :: Elt t => EltRepr t -> Boundary (Array sh t)
  Function :: (Shape sh, Elt e) => (sh -> e) -> Boundary (Array sh e)


evalPreBoundary :: EvalAcc acc -> AST.PreBoundary acc aenv t -> Val aenv -> Boundary t
evalPreBoundary evalAcc bnd aenv =
  case bnd of
    AST.Clamp      -> Clamp
    AST.Mirror     -> Mirror
    AST.Wrap       -> Wrap
    AST.Constant v -> Constant v
    AST.Function f -> Function (evalPreFun evalAcc f aenv)


-- Scalar expression evaluation
-- ----------------------------

-- Evaluate a closed scalar expression
--
evalPreExp :: EvalAcc acc -> PreExp acc aenv t -> Val aenv -> t
evalPreExp evalAcc e aenv = evalPreOpenExp evalAcc e EmptyElt aenv

-- Evaluate a closed scalar function
--
evalPreFun :: EvalAcc acc -> PreFun acc aenv t -> Val aenv -> t
evalPreFun evalAcc f aenv = evalPreOpenFun evalAcc f EmptyElt aenv

-- Evaluate an open scalar function
--
evalPreOpenFun :: EvalAcc acc -> PreOpenFun acc env aenv t -> ValElt env -> Val aenv -> t
evalPreOpenFun evalAcc (Body e) env aenv = evalPreOpenExp evalAcc e env aenv
evalPreOpenFun evalAcc (Lam f)  env aenv =
  \x -> evalPreOpenFun evalAcc f (env `PushElt` fromElt x) aenv


-- Evaluate an open scalar expression
--
-- NB: The implementation of 'Index' and 'Shape' demonstrate clearly why
--     array expressions must be hoisted out of scalar expressions before code
--     execution. If these operations are in the body of a function that gets
--     mapped over an array, the array argument would be evaluated many times
--     leading to a large amount of wasteful recomputation.
--
evalPreOpenExp
    :: forall acc env aenv t.
       EvalAcc acc
    -> PreOpenExp acc env aenv t
    -> ValElt env
    -> Val aenv
    -> t
evalPreOpenExp evalAcc pexp env aenv =
  let
      evalE :: PreOpenExp acc env aenv t' -> t'
      evalE e = evalPreOpenExp evalAcc e env aenv

      evalF :: PreOpenFun acc env aenv f' -> f'
      evalF f = evalPreOpenFun evalAcc f env aenv

      evalA :: acc aenv a -> a
      evalA a = evalAcc a aenv
  in
  case pexp of
    Let exp1 exp2               -> let !v1  = evalE exp1
                                       env' = env `PushElt` fromElt v1
                                   in  evalPreOpenExp evalAcc exp2 env' aenv
    Var ix                      -> prjElt ix env
    Const c                     -> toElt c
    Undef                       -> evalUndef
    PrimConst c                 -> evalPrimConst c
    PrimApp f x                 -> evalPrim f (evalE x)
    Tuple tup                   -> toTuple $ evalTuple evalAcc tup env aenv
    Prj ix tup                  -> evalPrj ix . fromTuple $ evalE tup
    IndexNil                    -> Z
    IndexAny                    -> Any
    IndexCons sh sz             -> evalE sh :. evalE sz
    IndexHead sh                -> let _  :. ix = evalE sh in ix
    IndexTail sh                -> let ix :. _  = evalE sh in ix
    IndexTrans sh               -> transpose (evalE sh)
    IndexSlice slice _slix sh   -> toElt $ restrict slice (fromElt (evalE sh))
      where
        restrict :: SliceIndex slix sl co sh -> sh -> sl
        restrict SliceNil              ()         = ()
        restrict (SliceAll sliceIdx)   (sl, sz)   =
          let sl' = restrict sliceIdx sl
          in  (sl', sz)
        restrict (SliceFixed sliceIdx) (sl, _sz) =
          restrict sliceIdx sl

    IndexFull slice slix sh     -> toElt $ extend slice (fromElt (evalE slix))
                                                        (fromElt (evalE sh))
      where
        extend :: SliceIndex slix sl co sh -> slix -> sl -> sh
        extend SliceNil              ()        ()       = ()
        extend (SliceAll sliceIdx)   (slx, ()) (sl, sz) =
          let sh' = extend sliceIdx slx sl
          in  (sh', sz)
        extend (SliceFixed sliceIdx) (slx, sz) sl       =
          let sh' = extend sliceIdx slx sl
          in  (sh', sz)

    ToIndex sh ix               -> toIndex (evalE sh) (evalE ix)
    FromIndex sh ix             -> fromIndex (evalE sh) (evalE ix)
    ToSlice _ sh ix             -> toSlice (evalE sh) (evalE ix)
    Cond c t e
      | evalE c                 -> evalE t
      | otherwise               -> evalE e

    While cond body seed        -> go (evalE seed)
      where
        f       = evalF body
        p       = evalF cond
        go !x
          | p x         = go (f x)
          | otherwise   = x

    Index acc ix                -> evalA acc ! evalE ix
    LinearIndex acc i           -> let a  = evalA acc
                                       ix = fromIndex (shape a) (evalE i)
                                   in a ! ix
    Shape acc                   -> shape (evalA acc)
    ShapeSize sh                -> size (evalE sh)
    Intersect sh1 sh2           -> intersect (evalE sh1) (evalE sh2)
    Union sh1 sh2               -> union (evalE sh1) (evalE sh2)
    Foreign _ f e               -> evalPreOpenFun evalAcc f EmptyElt Empty $ evalE e
    Coerce e                    -> evalCoerce (evalE e)


-- Constant values
-- ---------------

evalUndef :: forall a. Elt a => a
evalUndef = toElt (undef (eltType @a))
  where
    undef :: TupleType t -> t
    undef TypeRunit       = ()
    undef (TypeRpair a b) = (undef a, undef b)
    undef (TypeRscalar t) = scalar t

    scalar :: ScalarType t -> t
    scalar (SingleScalarType t) = single t
    scalar (VectorScalarType t) = vector t

    single :: SingleType t -> t
    single (NumSingleType    t) = num t
    single (NonNumSingleType t) = nonnum t

    vector :: VectorType t -> t
    vector (VectorType n t) = vec (n * sizeOfSingleType t)

    vec :: Int -> Vec n t
    vec n = runST $ do
      mba           <- newByteArray n
      ByteArray ba# <- unsafeFreezeByteArray mba
      return $ Vec ba#

    num :: NumType t -> t
    num (IntegralNumType t) | IntegralDict <- integralDict t = 0
    num (FloatingNumType t) | FloatingDict <- floatingDict t = 0

    nonnum :: NonNumType t -> t
    nonnum TypeBool{}   = False
    nonnum TypeChar{}   = chr 0


-- Coercions
-- ---------

evalCoerce :: forall a b. (Elt a, Elt b) => a -> b
evalCoerce = toElt . go (eltType @a) (eltType @b) . fromElt
  where
    go :: TupleType s -> TupleType t -> s -> t
    go TypeRunit        TypeRunit          ()    = ()
    go (TypeRpair s1 s2) (TypeRpair t1 t2) (x,y) = (go s1 t1 x, go s2 t2 y)
    go (TypeRscalar s)   (TypeRscalar t)   x
      = $internalCheck "evalCoerce" "sizes not equal" (sizeOfScalarType s == sizeOfScalarType t)
      $ evalCoerceScalar s t x
    --
    -- newtype wrappers are typically declared similarly to `EltRepr (T a) = ((), EltRepr a)'
    -- so add some special cases for dealing with redundant parentheses.
    --
    go (TypeRpair TypeRunit s) t@TypeRscalar{}         ((), x) = go s t x
    go s@TypeRscalar{}         (TypeRpair TypeRunit t) x       = ((), go s t x)
    --
    go _ _ _
      = error $ printf "could not coerce type `%s' to `%s'"
                  (show (typeOf (undefined::a)))
                  (show (typeOf (undefined::b)))


-- Coercion between two scalar types. We require that the size of the source and
-- destination values are equal (this is not checked at this point).
--
evalCoerceScalar :: ScalarType a -> ScalarType b -> a -> b
evalCoerceScalar SingleScalarType{}    SingleScalarType{} a = unsafeCoerce a
evalCoerceScalar VectorScalarType{}    VectorScalarType{} a = unsafeCoerce a  -- XXX: or just unpack/repack the (Vec ba#)
evalCoerceScalar (SingleScalarType ta) VectorScalarType{} a = vector ta a
  where
    vector :: SingleType a -> a -> Vec n b
    vector (NumSingleType    t) = num t
    vector (NonNumSingleType t) = nonnum t

    num :: NumType a -> a -> Vec n b
    num (IntegralNumType t) = integral t
    num (FloatingNumType t) = floating t

    integral :: IntegralType a -> a -> Vec n b
    integral TypeInt{}     = poke
    integral TypeInt8{}    = poke
    integral TypeInt16{}   = poke
    integral TypeInt32{}   = poke
    integral TypeInt64{}   = poke
    integral TypeWord{}    = poke
    integral TypeWord8{}   = poke
    integral TypeWord16{}  = poke
    integral TypeWord32{}  = poke
    integral TypeWord64{}  = poke

    floating :: FloatingType a -> a -> Vec n b
    floating TypeHalf{}    = poke
    floating TypeFloat{}   = poke
    floating TypeDouble{}  = poke

    nonnum :: NonNumType a -> a -> Vec n b
    nonnum TypeBool{}   = bool
    nonnum TypeChar{}   = poke

    bool :: Bool -> Vec n b
    bool False = poke (0::Word8)
    bool True  = poke (1::Word8)

    {-# INLINE poke #-}
    poke :: forall a b n. Prim a => a -> Vec n b
    poke x = runST $ do
      mba <- newByteArray (sizeOf (undefined::a))
      writeByteArray mba 0 x
      ByteArray ba# <- unsafeFreezeByteArray mba
      return $ Vec ba#

evalCoerceScalar VectorScalarType{} (SingleScalarType tb) a = scalar tb a
  where
    scalar :: SingleType b -> Vec n a -> b
    scalar (NumSingleType    t) = num t
    scalar (NonNumSingleType t) = nonnum t

    num :: NumType b -> Vec n a -> b
    num (IntegralNumType t) = integral t
    num (FloatingNumType t) = floating t

    integral :: IntegralType b -> Vec n a -> b
    integral TypeInt{}     = peek
    integral TypeInt8{}    = peek
    integral TypeInt16{}   = peek
    integral TypeInt32{}   = peek
    integral TypeInt64{}   = peek
    integral TypeWord{}    = peek
    integral TypeWord8{}   = peek
    integral TypeWord16{}  = peek
    integral TypeWord32{}  = peek
    integral TypeWord64{}  = peek

    floating :: FloatingType b -> Vec n a -> b
    floating TypeHalf{}    = peek
    floating TypeFloat{}   = peek
    floating TypeDouble{}  = peek

    nonnum :: NonNumType b -> Vec n a -> b
    nonnum TypeBool{}   = bool
    nonnum TypeChar{}   = peek

    bool :: Vec n a -> Bool
    bool v = case peek @Word8 v of
               0 -> False
               _ -> True

    {-# INLINE peek #-}
    peek :: Prim a => Vec n b -> a
    peek (Vec ba#) = indexByteArray (ByteArray ba#) 0


-- Scalar primitives
-- -----------------

evalPrimConst :: PrimConst a -> a
evalPrimConst (PrimMinBound ty) = evalMinBound ty
evalPrimConst (PrimMaxBound ty) = evalMaxBound ty
evalPrimConst (PrimPi       ty) = evalPi ty

evalPrim :: PrimFun (a -> r) -> (a -> r)
evalPrim (PrimAdd                ty) = evalAdd ty
evalPrim (PrimSub                ty) = evalSub ty
evalPrim (PrimMul                ty) = evalMul ty
evalPrim (PrimNeg                ty) = evalNeg ty
evalPrim (PrimAbs                ty) = evalAbs ty
evalPrim (PrimSig                ty) = evalSig ty
evalPrim (PrimQuot               ty) = evalQuot ty
evalPrim (PrimRem                ty) = evalRem ty
evalPrim (PrimQuotRem            ty) = evalQuotRem ty
evalPrim (PrimIDiv               ty) = evalIDiv ty
evalPrim (PrimMod                ty) = evalMod ty
evalPrim (PrimDivMod             ty) = evalDivMod ty
evalPrim (PrimBAnd               ty) = evalBAnd ty
evalPrim (PrimBOr                ty) = evalBOr ty
evalPrim (PrimBXor               ty) = evalBXor ty
evalPrim (PrimBNot               ty) = evalBNot ty
evalPrim (PrimBShiftL            ty) = evalBShiftL ty
evalPrim (PrimBShiftR            ty) = evalBShiftR ty
evalPrim (PrimBRotateL           ty) = evalBRotateL ty
evalPrim (PrimBRotateR           ty) = evalBRotateR ty
evalPrim (PrimPopCount           ty) = evalPopCount ty
evalPrim (PrimCountLeadingZeros  ty) = evalCountLeadingZeros ty
evalPrim (PrimCountTrailingZeros ty) = evalCountTrailingZeros ty
evalPrim (PrimFDiv               ty) = evalFDiv ty
evalPrim (PrimRecip              ty) = evalRecip ty
evalPrim (PrimSin                ty) = evalSin ty
evalPrim (PrimCos                ty) = evalCos ty
evalPrim (PrimTan                ty) = evalTan ty
evalPrim (PrimAsin               ty) = evalAsin ty
evalPrim (PrimAcos               ty) = evalAcos ty
evalPrim (PrimAtan               ty) = evalAtan ty
evalPrim (PrimSinh               ty) = evalSinh ty
evalPrim (PrimCosh               ty) = evalCosh ty
evalPrim (PrimTanh               ty) = evalTanh ty
evalPrim (PrimAsinh              ty) = evalAsinh ty
evalPrim (PrimAcosh              ty) = evalAcosh ty
evalPrim (PrimAtanh              ty) = evalAtanh ty
evalPrim (PrimExpFloating        ty) = evalExpFloating ty
evalPrim (PrimSqrt               ty) = evalSqrt ty
evalPrim (PrimLog                ty) = evalLog ty
evalPrim (PrimFPow               ty) = evalFPow ty
evalPrim (PrimLogBase            ty) = evalLogBase ty
evalPrim (PrimTruncate        ta tb) = evalTruncate ta tb
evalPrim (PrimRound           ta tb) = evalRound ta tb
evalPrim (PrimFloor           ta tb) = evalFloor ta tb
evalPrim (PrimCeiling         ta tb) = evalCeiling ta tb
evalPrim (PrimAtan2              ty) = evalAtan2 ty
evalPrim (PrimIsNaN              ty) = evalIsNaN ty
evalPrim (PrimIsInfinite         ty) = evalIsInfinite ty
evalPrim (PrimLt                 ty) = evalLt ty
evalPrim (PrimGt                 ty) = evalGt ty
evalPrim (PrimLtEq               ty) = evalLtEq ty
evalPrim (PrimGtEq               ty) = evalGtEq ty
evalPrim (PrimEq                 ty) = evalEq ty
evalPrim (PrimNEq                ty) = evalNEq ty
evalPrim (PrimMax                ty) = evalMax ty
evalPrim (PrimMin                ty) = evalMin ty
evalPrim PrimLAnd                    = evalLAnd
evalPrim PrimLOr                     = evalLOr
evalPrim PrimLNot                    = evalLNot
evalPrim PrimOrd                     = evalOrd
evalPrim PrimChr                     = evalChr
evalPrim PrimBoolToInt               = evalBoolToInt
evalPrim (PrimFromIntegral ta tb)    = evalFromIntegral ta tb
evalPrim (PrimToFloating ta tb)      = evalToFloating ta tb


-- Tuple construction and projection
-- ---------------------------------

evalTuple :: EvalAcc acc -> Tuple (PreOpenExp acc env aenv) t -> ValElt env -> Val aenv -> t
evalTuple _       NilTup            _env _aenv = ()
evalTuple evalAcc (tup `SnocTup` e) env  aenv  =
  (evalTuple evalAcc tup env aenv, evalPreOpenExp evalAcc e env aenv)

evalPrj :: TupleIdx t e -> t -> e
evalPrj ZeroTupIdx       (!_, v)   = v
evalPrj (SuccTupIdx idx) (tup, !_) = evalPrj idx tup
  -- FIXME: Strictly speaking, we ought to force all components of a tuples;
  --        not only those that we happen to encounter during the recursive
  --        walk.


-- Implementation of scalar primitives
-- -----------------------------------

evalLAnd :: (Bool, Bool) -> Bool
evalLAnd (x, y) = x && y

evalLOr  :: (Bool, Bool) -> Bool
evalLOr (x, y) = x || y

evalLNot :: Bool -> Bool
evalLNot = not

evalOrd :: Char -> Int
evalOrd = ord

evalChr :: Int -> Char
evalChr = chr

evalBoolToInt :: Bool -> Int
evalBoolToInt True  = 1
evalBoolToInt False = 0

evalFromIntegral :: IntegralType a -> NumType b -> a -> b
evalFromIntegral ta (IntegralNumType tb)
  | IntegralDict <- integralDict ta
  , IntegralDict <- integralDict tb
  = fromIntegral

evalFromIntegral ta (FloatingNumType tb)
  | IntegralDict <- integralDict ta
  , FloatingDict <- floatingDict tb
  = fromIntegral

evalToFloating :: NumType a -> FloatingType b -> a -> b
evalToFloating (IntegralNumType ta) tb
  | IntegralDict <- integralDict ta
  , FloatingDict <- floatingDict tb
  = realToFrac

evalToFloating (FloatingNumType ta) tb
  | FloatingDict <- floatingDict ta
  , FloatingDict <- floatingDict tb
  = realToFrac


-- Extract methods from reified dictionaries
--

-- Constant methods of Bounded
--

evalMinBound :: BoundedType a -> a
evalMinBound (IntegralBoundedType ty)
  | IntegralDict <- integralDict ty
  = minBound

evalMinBound (NonNumBoundedType   ty)
  | NonNumDict   <- nonNumDict ty
  = minBound

evalMaxBound :: BoundedType a -> a
evalMaxBound (IntegralBoundedType ty)
  | IntegralDict <- integralDict ty
  = maxBound

evalMaxBound (NonNumBoundedType   ty)
  | NonNumDict   <- nonNumDict ty
  = maxBound

-- Constant method of floating
--

evalPi :: FloatingType a -> a
evalPi ty | FloatingDict <- floatingDict ty = pi

evalSin :: FloatingType a -> (a -> a)
evalSin ty | FloatingDict <- floatingDict ty = sin

evalCos :: FloatingType a -> (a -> a)
evalCos ty | FloatingDict <- floatingDict ty = cos

evalTan :: FloatingType a -> (a -> a)
evalTan ty | FloatingDict <- floatingDict ty = tan

evalAsin :: FloatingType a -> (a -> a)
evalAsin ty | FloatingDict <- floatingDict ty = asin

evalAcos :: FloatingType a -> (a -> a)
evalAcos ty | FloatingDict <- floatingDict ty = acos

evalAtan :: FloatingType a -> (a -> a)
evalAtan ty | FloatingDict <- floatingDict ty = atan

evalSinh :: FloatingType a -> (a -> a)
evalSinh ty | FloatingDict <- floatingDict ty = sinh

evalCosh :: FloatingType a -> (a -> a)
evalCosh ty | FloatingDict <- floatingDict ty = cosh

evalTanh :: FloatingType a -> (a -> a)
evalTanh ty | FloatingDict <- floatingDict ty = tanh

evalAsinh :: FloatingType a -> (a -> a)
evalAsinh ty | FloatingDict <- floatingDict ty = asinh

evalAcosh :: FloatingType a -> (a -> a)
evalAcosh ty | FloatingDict <- floatingDict ty = acosh

evalAtanh :: FloatingType a -> (a -> a)
evalAtanh ty | FloatingDict <- floatingDict ty = atanh

evalExpFloating :: FloatingType a -> (a -> a)
evalExpFloating ty | FloatingDict <- floatingDict ty = exp

evalSqrt :: FloatingType a -> (a -> a)
evalSqrt ty | FloatingDict <- floatingDict ty = sqrt

evalLog :: FloatingType a -> (a -> a)
evalLog ty | FloatingDict <- floatingDict ty = log

evalFPow :: FloatingType a -> ((a, a) -> a)
evalFPow ty | FloatingDict <- floatingDict ty = uncurry (**)

evalLogBase :: FloatingType a -> ((a, a) -> a)
evalLogBase ty | FloatingDict <- floatingDict ty = uncurry logBase

evalTruncate :: FloatingType a -> IntegralType b -> (a -> b)
evalTruncate ta tb
  | FloatingDict <- floatingDict ta
  , IntegralDict <- integralDict tb
  = truncate

evalRound :: FloatingType a -> IntegralType b -> (a -> b)
evalRound ta tb
  | FloatingDict <- floatingDict ta
  , IntegralDict <- integralDict tb
  = round

evalFloor :: FloatingType a -> IntegralType b -> (a -> b)
evalFloor ta tb
  | FloatingDict <- floatingDict ta
  , IntegralDict <- integralDict tb
  = floor

evalCeiling :: FloatingType a -> IntegralType b -> (a -> b)
evalCeiling ta tb
  | FloatingDict <- floatingDict ta
  , IntegralDict <- integralDict tb
  = ceiling

evalAtan2 :: FloatingType a -> ((a, a) -> a)
evalAtan2 ty | FloatingDict <- floatingDict ty = uncurry atan2

evalIsNaN :: FloatingType a -> (a -> Bool)
evalIsNaN ty | FloatingDict <- floatingDict ty = isNaN

evalIsInfinite :: FloatingType a -> (a -> Bool)
evalIsInfinite ty | FloatingDict <- floatingDict ty = isInfinite


-- Methods of Num
--

evalAdd :: NumType a -> ((a, a) -> a)
evalAdd (IntegralNumType ty) | IntegralDict <- integralDict ty = uncurry (+)
evalAdd (FloatingNumType ty) | FloatingDict <- floatingDict ty = uncurry (+)

evalSub :: NumType a -> ((a, a) -> a)
evalSub (IntegralNumType ty) | IntegralDict <- integralDict ty = uncurry (-)
evalSub (FloatingNumType ty) | FloatingDict <- floatingDict ty = uncurry (-)

evalMul :: NumType a -> ((a, a) -> a)
evalMul (IntegralNumType ty) | IntegralDict <- integralDict ty = uncurry (*)
evalMul (FloatingNumType ty) | FloatingDict <- floatingDict ty = uncurry (*)

evalNeg :: NumType a -> (a -> a)
evalNeg (IntegralNumType ty) | IntegralDict <- integralDict ty = negate
evalNeg (FloatingNumType ty) | FloatingDict <- floatingDict ty = negate

evalAbs :: NumType a -> (a -> a)
evalAbs (IntegralNumType ty) | IntegralDict <- integralDict ty = abs
evalAbs (FloatingNumType ty) | FloatingDict <- floatingDict ty = abs

evalSig :: NumType a -> (a -> a)
evalSig (IntegralNumType ty) | IntegralDict <- integralDict ty = signum
evalSig (FloatingNumType ty) | FloatingDict <- floatingDict ty = signum

evalQuot :: IntegralType a -> ((a, a) -> a)
evalQuot ty | IntegralDict <- integralDict ty = uncurry quot

evalRem :: IntegralType a -> ((a, a) -> a)
evalRem ty | IntegralDict <- integralDict ty = uncurry rem

evalQuotRem :: IntegralType a -> ((a, a) -> (a, a))
evalQuotRem ty | IntegralDict <- integralDict ty = uncurry quotRem

evalIDiv :: IntegralType a -> ((a, a) -> a)
evalIDiv ty | IntegralDict <- integralDict ty = uncurry div

evalMod :: IntegralType a -> ((a, a) -> a)
evalMod ty | IntegralDict <- integralDict ty = uncurry mod

evalDivMod :: IntegralType a -> ((a, a) -> (a, a))
evalDivMod ty | IntegralDict <- integralDict ty = uncurry divMod

evalBAnd :: IntegralType a -> ((a, a) -> a)
evalBAnd ty | IntegralDict <- integralDict ty = uncurry (.&.)

evalBOr :: IntegralType a -> ((a, a) -> a)
evalBOr ty | IntegralDict <- integralDict ty = uncurry (.|.)

evalBXor :: IntegralType a -> ((a, a) -> a)
evalBXor ty | IntegralDict <- integralDict ty = uncurry xor

evalBNot :: IntegralType a -> (a -> a)
evalBNot ty | IntegralDict <- integralDict ty = complement

evalBShiftL :: IntegralType a -> ((a, Int) -> a)
evalBShiftL ty | IntegralDict <- integralDict ty = uncurry shiftL

evalBShiftR :: IntegralType a -> ((a, Int) -> a)
evalBShiftR ty | IntegralDict <- integralDict ty = uncurry shiftR

evalBRotateL :: IntegralType a -> ((a, Int) -> a)
evalBRotateL ty | IntegralDict <- integralDict ty = uncurry rotateL

evalBRotateR :: IntegralType a -> ((a, Int) -> a)
evalBRotateR ty | IntegralDict <- integralDict ty = uncurry rotateR

evalPopCount :: IntegralType a -> (a -> Int)
evalPopCount ty | IntegralDict <- integralDict ty = popCount

evalCountLeadingZeros :: IntegralType a -> (a -> Int)
#if __GLASGOW_HASKELL__ >= 710
evalCountLeadingZeros ty | IntegralDict <- integralDict ty = countLeadingZeros
#else
evalCountLeadingZeros ty | IntegralDict <- integralDict ty = clz
  where
    clz x = (w-1) - go (w-1)
      where
        go i | i < 0       = i  -- no bit set
             | testBit x i = i
             | otherwise   = go (i-1)
        w = finiteBitSize x
#endif

evalCountTrailingZeros :: IntegralType a -> (a -> Int)
#if __GLASGOW_HASKELL__ >= 710
evalCountTrailingZeros ty | IntegralDict <- integralDict ty = countTrailingZeros
#else
evalCountTrailingZeros ty | IntegralDict <- integralDict ty = ctz
  where
    ctz x = go 0
      where
        go i | i >= w      = i
             | testBit x i = i
             | otherwise   = go (i+1)
        w = finiteBitSize x
#endif


evalFDiv :: FloatingType a -> ((a, a) -> a)
evalFDiv ty | FloatingDict <- floatingDict ty = uncurry (/)

evalRecip :: FloatingType a -> (a -> a)
evalRecip ty | FloatingDict <- floatingDict ty = recip


evalLt :: SingleType a -> ((a, a) -> Bool)
evalLt (NumSingleType (IntegralNumType ty)) | IntegralDict <- integralDict ty = uncurry (<)
evalLt (NumSingleType (FloatingNumType ty)) | FloatingDict <- floatingDict ty = uncurry (<)
evalLt (NonNumSingleType ty)                | NonNumDict   <- nonNumDict ty   = uncurry (<)

evalGt :: SingleType a -> ((a, a) -> Bool)
evalGt (NumSingleType (IntegralNumType ty)) | IntegralDict <- integralDict ty = uncurry (>)
evalGt (NumSingleType (FloatingNumType ty)) | FloatingDict <- floatingDict ty = uncurry (>)
evalGt (NonNumSingleType ty)                | NonNumDict   <- nonNumDict ty   = uncurry (>)

evalLtEq :: SingleType a -> ((a, a) -> Bool)
evalLtEq (NumSingleType (IntegralNumType ty)) | IntegralDict <- integralDict ty = uncurry (<=)
evalLtEq (NumSingleType (FloatingNumType ty)) | FloatingDict <- floatingDict ty = uncurry (<=)
evalLtEq (NonNumSingleType ty)                | NonNumDict   <- nonNumDict ty   = uncurry (<=)

evalGtEq :: SingleType a -> ((a, a) -> Bool)
evalGtEq (NumSingleType (IntegralNumType ty)) | IntegralDict <- integralDict ty = uncurry (>=)
evalGtEq (NumSingleType (FloatingNumType ty)) | FloatingDict <- floatingDict ty = uncurry (>=)
evalGtEq (NonNumSingleType ty)                | NonNumDict   <- nonNumDict ty   = uncurry (>=)

evalEq :: SingleType a -> ((a, a) -> Bool)
evalEq (NumSingleType (IntegralNumType ty)) | IntegralDict <- integralDict ty = uncurry (==)
evalEq (NumSingleType (FloatingNumType ty)) | FloatingDict <- floatingDict ty = uncurry (==)
evalEq (NonNumSingleType ty)                | NonNumDict   <- nonNumDict ty   = uncurry (==)

evalNEq :: SingleType a -> ((a, a) -> Bool)
evalNEq (NumSingleType (IntegralNumType ty)) | IntegralDict <- integralDict ty = uncurry (/=)
evalNEq (NumSingleType (FloatingNumType ty)) | FloatingDict <- floatingDict ty = uncurry (/=)
evalNEq (NonNumSingleType ty)                | NonNumDict   <- nonNumDict ty   = uncurry (/=)

evalMax :: SingleType a -> ((a, a) -> a)
evalMax (NumSingleType (IntegralNumType ty)) | IntegralDict <- integralDict ty = uncurry max
evalMax (NumSingleType (FloatingNumType ty)) | FloatingDict <- floatingDict ty = uncurry max
evalMax (NonNumSingleType ty)                | NonNumDict   <- nonNumDict ty   = uncurry max

evalMin :: SingleType a -> ((a, a) -> a)
evalMin (NumSingleType (IntegralNumType ty)) | IntegralDict <- integralDict ty = uncurry min
evalMin (NumSingleType (FloatingNumType ty)) | FloatingDict <- floatingDict ty = uncurry min
evalMin (NonNumSingleType ty)                | NonNumDict   <- nonNumDict ty   = uncurry min


-- Sequence evaluation
-- ---------------

mAXIMUM_CHUNK_SIZE :: Int
mAXIMUM_CHUNK_SIZE = 1024

evalDelayedSeq :: DelayedSeq arrs
               -> arrs
evalDelayedSeq (StreamSeq aenv s) | aenv' <- evalExtend aenv Empty
                                  = evalSeq 1 Nothing Nothing s aenv'

evalSeq :: forall index aenv arrs. SeqIndex index
        => Int
        -> Maybe Int
        -> Maybe Int
        -> PreOpenSeq index DelayedOpenAcc aenv arrs
        -> Val aenv
        -> arrs
evalSeq min max i s aenv = evalSeq' BaseEnv s
  where
    evalSeq' :: forall aenv'. Extend (Producer index DelayedOpenAcc) aenv aenv' -> PreOpenSeq index DelayedOpenAcc aenv' arrs -> arrs
    evalSeq' prods s =
      case s of
        Producer (Pull src) s -> evalSeq' (PushEnv prods (Pull src)) s
        Producer (ProduceAccum l f a) (Consumer (Last a' d)) -> last $
          go i
            index
            (evalPreExp evalOpenAcc <$> l <*> pure aenv')
            (evalOpenAfun f)
            (evalOpenAcc a aenv')
            [evalOpenAcc (fromJust (strengthen (drop Just) d)) aenv']
            (evalOpenAcc a')
            ext
            (Just aenv')
        Producer (ProduceAccum l f a) (Reify ty a') -> concatMap (divide ty) $
          go i
            index
            (evalPreExp evalOpenAcc <$> l <*> pure aenv')
            (evalOpenAfun f)
            (evalOpenAcc a aenv')
            []
            (evalOpenAcc a')
            ext
            (Just aenv')
        _ -> $internalError "evalSeq" "Sequence computation does not appear to be delayed"
      where
        (ext, Just aenv') = evalSources (indexSize index) prods
        index             = evalPreExp evalOpenAcc (initialIndex (Const min)) aenv'
        go :: forall arrs s a. Maybe Int
           -> index
           -> Maybe Int
           -> (Val aenv' -> Scalar index -> s -> (a, s))
           -> s
           -> [arrs]
           -> (Val (aenv', a) -> arrs)
           -> Extend (Producer index DelayedOpenAcc) aenv aenv'
           -> Maybe (Val aenv')
           -> [arrs]
        go _ _     _ _ _ a _    _   Nothing      = a
        go i index l f s a next ext (Just aenv') =
          let
            (a', s') = f aenv' (fromFunction Z (const index)) s
            a''      = next (aenv' `Push` a')
            index'   = nextIndex' index
            (ext', maenv) = evalSources (indexSize index') ext
          in if maybe True (contains' index) l && maybe True (>0) i
              then a'' : go (flip (-) 1 <$> i)
                            index' l f s' [] next ext' maenv
              else a

        nextIndex'= modifySize (\n -> if 2*n <= fromMaybe mAXIMUM_CHUNK_SIZE max
                                      then 2*n
                                      else n)
                  . nextIndex

    drop :: forall aenv aenv' a. aenv' :?> aenv -> (aenv',a) :?> aenv
    drop _ ZeroIdx      = Nothing
    drop v (SuccIdx ix) = v ix

    evalSources :: Int
                -> Extend (Producer index DelayedOpenAcc) aenv aenv'
                -> (Extend (Producer index DelayedOpenAcc) aenv aenv', Maybe (Val aenv'))
    -- evalSources n (PushEnv ext (Pull (Function f a)))  -- XXX Merge artefact
    --   | (ext', aenv) <- evalSources n ext
    --   , (stop,b,a') <- f n a
    --   = ( PushEnv ext' (Pull (Function f a'))
    --     , if not stop then Push <$> aenv <*> pure b else Nothing)
    evalSources _ BaseEnv
      = (BaseEnv, Just aenv)
    evalSources _ _
      = $internalError "evalSeq" "AST is at wrong stage"


evalExtend :: Extend DelayedOpenAcc aenv aenv' -> Val aenv -> Val aenv'
evalExtend BaseEnv aenv = aenv
evalExtend (PushEnv ext1 ext2) aenv | aenv' <- evalExtend ext1 aenv

                                    = Push aenv' (evalOpenAcc ext2 aenv')
