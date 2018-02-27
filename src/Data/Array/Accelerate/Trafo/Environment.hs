{-# LANGUAGE GADTs               #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell     #-}
{-# LANGUAGE TypeOperators       #-}
-- |
-- Module      : Data.Array.Accelerate.Trafo.Environment
-- Copyright   : [2012..2018] Trevor L. McDonell
-- License     : BSD3
--
-- Maintainer  : Trevor L. McDonell <tmcdonell@cse.unsw.edu.au>
-- Stability   : experimental
-- Portability : non-portable (GHC extensions)
--

module Data.Array.Accelerate.Trafo.Environment
  where

import Data.Array.Accelerate.AST
import Data.Array.Accelerate.Array.Sugar
import Data.Array.Accelerate.Error
import Data.Array.Accelerate.Trafo.Base
import Data.Array.Accelerate.Trafo.Substitution

import Data.Array.Accelerate.Debug.Stats                as Stats


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
-- variable does no less work than weakening by multiple variables at once; both
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

{--
lookupExp
    :: Kit acc
    => Gamma      acc env env' aenv
    -> PreOpenExp acc env      aenv t
    -> Maybe (Idx env' t)
lookupExp EmptyExp        _ = Nothing
lookupExp (PushExp env e) x
  | Just Refl <- match e x  = Just ZeroIdx
  | otherwise               = SuccIdx `fmap` lookupExp env x

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
     => Extend     acc aenv aenv'
     -> PreOpenAcc acc      aenv' a
     -> PreOpenAcc acc aenv       a
bind BaseEnv         = id
bind (PushEnv env a) = bind env . Alet a . inject

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


{--
-- This is the same as Extend, but for the scalar environment.
--
data Supplement acc env env' aenv where
  BaseSup :: Supplement acc env env aenv

  PushSup :: Elt e
          => Supplement acc env env'      aenv
          -> PreOpenExp acc     env'      aenv e
          -> Supplement acc env (env', e) aenv

bindExps
    :: (Kit acc, Elt e)
    => Supplement acc env env' aenv
    -> PreOpenExp acc env' aenv e
    -> PreOpenExp acc env  aenv e
bindExps BaseSup       = id
bindExps (PushSup g b) = bindExps g . Let b
--}

