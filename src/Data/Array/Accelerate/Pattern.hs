{-# LANGUAGE ConstraintKinds       #-}
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ParallelListComp      #-}
{-# LANGUAGE PatternSynonyms       #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TemplateHaskell       #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE UndecidableInstances  #-}
{-# LANGUAGE ViewPatterns          #-}
-- |
-- Module      : Data.Array.Accelerate.Pattern
-- Copyright   : [2018..2020] The Accelerate Team
-- License     : BSD3
--
-- Maintainer  : Trevor L. McDonell <trevor.mcdonell@gmail.com>
-- Stability   : experimental
-- Portability : non-portable (GHC extensions)
--

module Data.Array.Accelerate.Pattern (

  pattern Pattern,
  pattern T2,  pattern T3,  pattern T4,  pattern T5,  pattern T6,
  pattern T7,  pattern T8,  pattern T9,  pattern T10, pattern T11,
  pattern T12, pattern T13, pattern T14, pattern T15, pattern T16,

  pattern I0, pattern I1, pattern I2, pattern I3, pattern I4,
  pattern I5, pattern I6, pattern I7, pattern I8, pattern I9,

  pattern SIMD,
  pattern V2, pattern V3, pattern V4, pattern V8, pattern V16,

) where

import Data.Array.Accelerate.AST.Idx
import Data.Array.Accelerate.Pattern.Shape
import Data.Array.Accelerate.Representation.Tag
import Data.Array.Accelerate.Smart
import Data.Array.Accelerate.Sugar.Array
import Data.Array.Accelerate.Sugar.Elt
-- import Data.Array.Accelerate.Sugar.Shape
import Data.Array.Accelerate.Sugar.Vec
import Data.Array.Accelerate.Type

import Language.Haskell.TH.Extra                                    hiding ( Exp, Match )


-- | A pattern synonym for working with (product) data types. You can declare
-- your own pattern synonyms based off of this.
--
pattern Pattern :: forall b a context. IsPattern context a b => b -> context a
pattern Pattern vars <- (matcher @context -> vars)
  where Pattern = builder @context
{-# COMPLETE Pattern :: Exp #-}
{-# COMPLETE Pattern :: Acc #-}

class IsPattern context a b where
  builder :: b -> context a
  matcher :: context a -> b


pattern SIMD :: forall b a context. IsSIMD context a b => b -> context a
pattern SIMD vars <- (vmatcher @context -> vars)
  where SIMD = vbuilder @context

class IsSIMD context a b where
  vbuilder :: b -> context a
  vmatcher :: context a -> b


-- IsPattern instances for up to 16-tuples (Acc and Exp). TH takes care of
-- the (unremarkable) boilerplate for us.
--
runQ $ do
    let
        -- Generate instance declarations for IsPattern of the form:
        -- instance (Arrays x, ArraysR x ~ (((), ArraysR a), ArraysR b), Arrays a, Arrays b,) => IsPattern Acc x (Acc a, Acc b)
        mkAccPattern :: Int -> Q [Dec]
        mkAccPattern n = do
          a  <- newName "a"
          _x <- newName "_x"
          let
              -- Type variables for the elements
              xs       = [ mkName ('x' : show i) | i <- [0 .. n-1] ]
              -- Last argument to `IsPattern`, eg (Acc a, Acc b) in the example
              b        = tupT (map (\t -> [t| Acc $(varT t)|]) xs)
              -- Representation as snoc-list of pairs, eg (((), ArraysR a), ArraysR b)
              snoc     = foldl (\sn t -> [t| ($sn, ArraysR $(varT t)) |]) [t| () |] xs
              -- Constraints for the type class, consisting of Arrays constraints on all type variables,
              -- and an equality constraint on the representation type of `a` and the snoc representation `snoc`.
              context  = tupT
                       $ [t| Arrays $(varT a) |]
                       : [t| ArraysR $(varT a) ~ $snoc |]
                       : map (\t -> [t| Arrays $(varT t)|]) xs
              --
              get x 0 = [| Acc (SmartAcc (Aprj PairIdxRight $x)) |]
              get x i = get  [| SmartAcc (Aprj PairIdxLeft $x) |] (i-1)
          --
          [d| instance $context => IsPattern Acc $(varT a) $b where
                builder $(tupP (map (\x -> [p| Acc $(varP x)|]) xs)) =
                  Acc $(foldl (\vs v -> [| SmartAcc ($vs `Apair` $(varE v)) |]) [| SmartAcc Anil |] xs)
                matcher (Acc $(varP _x)) =
                  $(tupE (map (get (varE _x)) [(n-1), (n-2) .. 0]))
            |]

        -- Generate instance declarations for IsPattern of the form:
        -- instance (Elt x, EltR x ~ (((), EltR a), EltR b), Elt a, Elt b,) => IsPattern Exp x (Exp a, Exp b)
        mkExpPattern :: Int -> Q [Dec]
        mkExpPattern n = do
          a  <- newName "a"
          _x <- newName "_x"
          _y <- newName "_y"
          let
              -- Type variables for the elements
              xs       = [ mkName ('x' : show i) | i <- [0 .. n-1] ]
              -- Variables for sub-pattern matches
              ms       = [ mkName ('m' : show i) | i <- [0 .. n-1] ]
              tags     = foldl (\ts t -> [p| $ts `TagRpair` $(varP t) |]) [p| TagRunit |] ms
              -- Last argument to `IsPattern`, eg (Exp, a, Exp b) in the example
              b        = tupT (map (\t -> [t| Exp $(varT t)|]) xs)
              -- Representation as snoc-list of pairs, eg (((), EltR a), EltR b)
              snoc     = foldl (\sn t -> [t| ($sn, EltR $(varT t)) |]) [t| () |] xs
              -- Constraints for the type class, consisting of Elt constraints on all type variables,
              -- and an equality constraint on the representation type of `a` and the snoc representation `snoc`.
              context  = tupT
                       $ [t| Elt $(varT a) |]
                       : [t| EltR $(varT a) ~ $snoc |]
                       : map (\t -> [t| Elt $(varT t)|]) xs
              --
              get x 0 =     [| SmartExp (Prj PairIdxRight $x) |]
              get x i = get [| SmartExp (Prj PairIdxLeft $x)  |] (i-1)
          --
          [d| instance $context => IsPattern Exp $(varT a) $b where
                builder $(tupP (map (\x -> [p| Exp $(varP x)|]) xs)) =
                  let _unmatch :: SmartExp a -> SmartExp a
                      _unmatch (SmartExp (Match _ $(varP _y))) = $(varE _y)
                      _unmatch x = x
                  in
                  Exp $(foldl (\vs v -> [| SmartExp ($vs `Pair` _unmatch $(varE v)) |]) [| SmartExp Nil |] xs)
                matcher (Exp $(varP _x)) =
                  case $(varE _x) of
                    SmartExp (Match $tags $(varP _y))
                      -> $(tupE [[| Exp (SmartExp (Match $(varE m) $(get (varE _x) i))) |] | m <- ms | i <- [(n-1), (n-2) .. 0]])
                    _ -> $(tupE [[| Exp $(get (varE _x) i) |] | i <- [(n-1), (n-2) .. 0]])
            |]

        -- Generate instance declarations for IsSIMD of the form:
        -- instance (Elt a, Elt v, EltR v ~ VecR n a) => IsSIMD Exp v (Exp a, Exp a)
        mkVecPattern :: Int -> Q [Dec]
        mkVecPattern n = do
          a  <- newName "a"
          v  <- newName "v"
          _x <- newName "_x"
          _y <- newName "_y"
          let
              aT       = varT a
              vT       = varT v
              nT       = litT (numTyLit (toInteger n))
              -- Last argument to `IsSIMD`, eg (Exp, a, Exp a) in the example
              tup      = tupT (replicate n ([t| Exp $aT |]))
              -- Constraints for the type class, consisting of the Elt
              -- constraints and the equality on representation types
              context  = [t| (Elt $aT, Elt $vT, SIMD $nT $aT, EltR $vT ~ VecR $nT $aT) |]
              -- Type variables for the elements
              xs       = [ mkName ('x' : show i) | i <- [0 .. n-1] ]
              -- Variables for sub-pattern matches
              -- ms       = [ mkName ('m' : show i) | i <- [0 .. n-1] ]
              -- tags     = foldl (\ts t -> [p| $ts `TagRpair` $(varP t) |]) [p| TagRunit |] ms
          --
          [d| instance $context => IsSIMD Exp $vT $tup where
                vbuilder $(tupP (map (\x -> [p| Exp $(varP x)|]) xs)) =
                  let _unmatch :: SmartExp a -> SmartExp a
                      _unmatch (SmartExp (Match _ $(varP _y))) = $(varE _y)
                      _unmatch x = x
                  in
                  Exp $(foldl (\vs (i, x) -> [| mkInsert
                                                  $(varE 'vecR `appTypeE` nT `appTypeE` aT)
                                                  $(varE 'eltR `appTypeE` aT)
                                                  TypeWord8
                                                  $vs
                                                  (SmartExp (Const (NumScalarType (IntegralNumType (SingleIntegralType TypeWord8))) i))
                                                  (_unmatch $(varE x))
                                              |])
                          [| unExp (undef :: Exp (Vec $nT $aT)) |]
                          (zip [0 .. n-1] xs)
                   )

                vmatcher (Exp $(varP _x)) =
                  case $(varE _x) of
                    -- SmartExp (Match $tags $(varP _y))
                    --   -> $(tupE [[| Exp (SmartExp (Match $(varE m) (unExp (extract (Exp $(varE _x) :: Exp $vec) (constant (i :: Word8)))))) |] | m <- ms | i <- [0 .. n-1]])
                    --   -> $(tupE [[| Exp (SmartExp (Match $(varE m) (mkExtract
                    --                   $(varE 'vecR `appTypeE` nT `appTypeE` aT)
                    --                   $(varE 'eltR `appTypeE` aT)
                    --                   TypeWord8
                    --                   $(varE _x)
                    --                   (SmartExp (Const (NumScalarType (IntegralNumType (SingleIntegralType TypeWord8))) i))))) |]
                    --             | m <- ms
                    --             | i <- [0 .. n-1] ])

                    _ -> $(tupE [[| Exp $ mkExtract
                                      $(varE 'vecR `appTypeE` nT `appTypeE` aT)
                                      $(varE 'eltR `appTypeE` aT)
                                      TypeWord8
                                      $(varE _x)
                                      (SmartExp (Const (NumScalarType (IntegralNumType (SingleIntegralType TypeWord8))) i))
                                  |]
                                | i <- [0 .. n-1] ])
            |]

{--
        -- Generate instance declarations for IsVector of the form:
        -- instance (Elt v, EltR v ~ Vec 2 a, Elt a) => IsVector Exp v (Exp a, Exp a)
        mkVecPattern :: Int -> Q [Dec]
        mkVecPattern n = do
          a <- newName "a"
          v <- newName "v"
          let
              -- Last argument to `IsVector`, eg (Exp, a, Exp a) in the example
              tup      = tupT (replicate n ([t| Exp $(varT a)|]))
              -- Representation as a vector, eg (Vec 2 a)
              vec      = [t| Vec $(litT (numTyLit (fromIntegral n))) $(varT a) |]
              -- Constraints for the type class, consisting of Elt constraints on all type variables,
              -- and an equality constraint on the representation type of `a` and the vector representation `vec`.
              context  = [t| (Elt $(varT v), VecElt $(varT a), EltR $(varT v) ~ $vec) |]
              --
              vecR     = foldr appE ([| VecRnil |] `appE` (varE 'singleType `appTypeE` varT a)) (replicate n [| VecRsucc |])
              tR       = tupT (replicate n (varT a))
          --
          [d| instance $context => IsVector Exp $(varT v) $tup where
                vpack x = case builder x :: Exp $tR of
                            Exp x' -> Exp (SmartExp (VecPack $vecR x'))
                vunpack (Exp x) = matcher (Exp (SmartExp (VecUnpack $vecR x)) :: Exp $tR)
            |]
--}
    --
    es <- mapM mkExpPattern [0..16]
    as <- mapM mkAccPattern [0..16]
    vs <- mapM mkVecPattern [2,3,4,8,16]
    return $ concat (es ++ as++ vs)


-- | Specialised pattern synonyms for tuples, which may be more convenient to
-- use than 'Data.Array.Accelerate.Lift.lift' and
-- 'Data.Array.Accelerate.Lift.unlift'. For example, to construct a pair:
--
-- > let a = 4        :: Exp Int
-- > let b = 2        :: Exp Float
-- > let c = T2 a b   -- :: Exp (Int, Float); equivalent to 'lift (a,b)'
--
-- Similarly they can be used to destruct values:
--
-- > let T2 x y = c   -- x :: Exp Int, y :: Exp Float; equivalent to 'let (x,y) = unlift c'
--
-- These pattern synonyms can be used for both 'Exp' and 'Acc' terms.
--
-- Similarly, we have patterns for constructing and destructing indices of
-- a given dimensionality:
--
-- > let ix = Ix 2 3    -- :: Exp DIM2
-- > let I2 y x = ix    -- y :: Exp Int, x :: Exp Int
--
runQ $ do
    let
        mkT :: Int -> Q [Dec]
        mkT n =
          let xs    = [ mkName ('x' : show i) | i <- [0 .. n-1] ]
              ts    = map varT xs
              name  = mkName ('T':show n)
              con   = varT (mkName "con")
              ty1   = tupT ts
              ty2   = tupT (map (con `appT`) ts)
              sig   = foldr (\t r -> [t| $con $t -> $r |]) (appT con ty1) ts
          in
          sequence
            [ patSynSigD name [t| IsPattern $con $ty1 $ty2 => $sig |]
            , patSynD    name (prefixPatSyn xs) implBidir [p| Pattern $(tupP (map varP xs)) |]
            , pragCompleteD [name] (Just ''Acc)
            , pragCompleteD [name] (Just ''Exp)
            ]

        mkV :: Int -> Q [Dec]
        mkV n =
          let xs    = [ mkName ('x' : show i) | i <- [0 .. n-1] ]
              a     = varT (mkName "a")
              ts    = replicate n a
              name  = mkName ('V':show n)
              tup   = tupT (map (\t -> [t| Exp $t |]) ts)
              vec   = [t| Vec $(litT (numTyLit (toInteger n))) $a |]
              cst   = [t| (Elt $a, SIMD $(litT (numTyLit (toInteger n))) $a, IsSIMD Exp $vec $tup) |]
              sig   = foldr (\t r -> [t| Exp $t -> $r |]) [t| Exp $vec |] ts
          in
          sequence
            [ patSynSigD name [t| $cst => $sig |]
            , patSynD    name (prefixPatSyn xs) implBidir [p| SIMD $(tupP (map varP xs)) |]
            , pragCompleteD [name] Nothing
            ]

        mkI :: Int -> Q [Dec]
        mkI n =
          let xs      = [ mkName ('x' : show i) | i <- [0 .. n-1] ]
              ts      = map varT xs
              name    = mkName ('I':show n)
              ix      = mkName ":."
              cst     = tupT (map (\t -> [t| Elt $t |]) ts)
              dim     = foldl (\h t -> [t| $h :. $t |]) [t| Z |] ts
              sig     = foldr (\t r -> [t| Exp $t -> $r |]) [t| Exp $dim |] ts
          in
          sequence
            [ patSynSigD name [t| $cst => $sig |]
            , patSynD    name (prefixPatSyn xs) implBidir (foldl (\ps p -> infixP ps ix (varP p)) [p| Z |] xs)
            , pragCompleteD [name] Nothing
            ]

{--
        mkV :: Int -> Q [Dec]
        mkV n =
          let xs    = [ mkName ('x' : show i) | i <- [0 .. n-1] ]
              ts    = map varT xs
              name  = mkName ('V':show n)
              con   = varT (mkName "con")
              ty1   = varT (mkName "vec")
              ty2   = tupT (map (con `appT`) ts)
              sig   = foldr (\t r -> [t| $con $t -> $r |]) (appT con ty1) ts
          in
          sequence
            [ patSynSigD name [t| IsVector $con $ty1 $ty2 => $sig |]
            , patSynD    name (prefixPatSyn xs) implBidir [p| Vector $(tupP (map varP xs)) |]
            , pragCompleteD [name] (Just ''Exp)
            ]
--}
    --
    ts <- mapM mkT [2..16]
    is <- mapM mkI [0..9]
    vs <- mapM mkV [2,3,4,8,16]
    return $ concat (ts ++ is ++ vs)

