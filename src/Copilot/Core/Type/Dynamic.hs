--------------------------------------------------------------------------------
-- Copyright © 2011 National Institute of Aerospace / Galois, Inc.
--------------------------------------------------------------------------------

{-# LANGUAGE Safe #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE Rank2Types #-}

-- | An implementation of dynamic types using "Copilot.Core.Type.Equality".
-- The theory behind this technique is described the following paper:
--
-- * Baars, Arthur I. and Swierstra, S. Doaitse,
-- \"/Typing dynamic typing/\",
-- ACM SIGPLAN Notices vol. 37, p. 157-166, 2002

{-# LANGUAGE GADTs, KindSignatures, ScopedTypeVariables #-}

module Copilot.Core.Type.Dynamic
  ( Dynamic  (..)
  , DynamicF (..)
  , toDyn
  , fromDyn
  , toDynF
  , fromDynF
  ) where

import Copilot.Core.Type.Equality

--------------------------------------------------------------------------------

data Dynamic :: (* -> *) -> * where
  Dynamic :: a -> t a -> Dynamic t

data DynamicF :: (* -> *) -> (* -> *) -> * where
  DynamicF :: f a -> t a -> DynamicF f t

toDyn :: EqualType t => t a -> a -> Dynamic t
toDyn t x = Dynamic x t

fromDyn :: EqualType t => t a -> Dynamic t -> Maybe a
fromDyn t1 (Dynamic x t2) =
  case t1 =~= t2 of
    Just Refl -> return x
    Nothing   -> Nothing

toDynF :: EqualType t => t a -> f a -> DynamicF f t
toDynF t fx = DynamicF fx t

fromDynF :: EqualType t => t a -> DynamicF f t -> Maybe (f a)
fromDynF t1 (DynamicF fx t2) =
  case t1 =~= t2 of
    Just Refl -> return fx
    Nothing   -> Nothing
