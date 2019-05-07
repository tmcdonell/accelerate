{-# LANGUAGE GADTs #-}
-- |
-- Module      : Data.Array.Accelerate.Trafo.Environment
-- Copyright   : [2012..2019] The Accelerate Team
-- License     : BSD3
--
-- Maintainer  : Trevor L. McDonell <trevor.mcdonell@gmail.com>
-- Stability   : experimental
-- Portability : non-portable (GHC extensions)
--

module Data.Array.Accelerate.Trafo.Environment
  where

import Data.Array.Accelerate.Array.Sugar


data Extend acc aenv aenv' where
  BaseEnv :: Extend acc aenv aenv

  PushEnv :: Arrays a
          => Extend acc aenv aenv' -> acc aenv' a -> Extend acc aenv (aenv', a)

