--------------------------------------------------------------------------------
-- Copyright © 2011 National Institute of Aerospace / Galois, Inc.
--------------------------------------------------------------------------------

{-# LANGUAGE Safe #-}
{-# LANGUAGE GADTs, ExistentialQuantification #-}

module Copilot.Core.Random.Gen
  ( Gen
  , runGen
  , randomFromType
  , oneOf
  , freq
  , choose
  , elements
  , depth
  , weights
  , incDepth
  , randomReplicate
  ) where

import Copilot.Core.Random.Weights
import Copilot.Core.Error
import Copilot.Core.Type

import Control.Applicative
import Control.Monad
import System.Random (StdGen, Random, random, randomR, split)

--------------------------------------------------------------------------------

-- | @runGen@ takes a @Gen a@, a max depth of the expression, the weights, and
-- the standard random generator.
newtype Gen a = MkGen { runGen :: Depth -> Weights -> StdGen -> a }

instance Functor Gen where
  fmap f (MkGen h) = MkGen (\ d ws r -> f (h d ws r))

instance Applicative Gen where
  pure = return
  (<*>) = ap

instance Monad Gen where
  return x = MkGen (\ _ _ _ -> x)
  MkGen m >>= k = MkGen $ \ d ws r ->
    let (r1, r2) = split r       in
    let MkGen m' = k (m d ws r1) in
    m' d ws r2

--------------------------------------------------------------------------------

stdGen :: Gen StdGen
stdGen = MkGen $ \ _ _ g -> g

depth :: Gen Depth
depth = MkGen $ \ d _ _ -> d

weights :: Gen Weights
weights = MkGen $ \ _ ws _ -> ws

incDepth :: Gen a -> Gen a
incDepth gen = MkGen $ \ d ws g -> runGen gen (succ d) ws g

--------------------------------------------------------------------------------

randomFromType :: Type a -> Gen a
randomFromType t =
  case t of
    Bool   -> genBool
    Int8   -> genBoundedIntegral
    Int16  -> genBoundedIntegral
    Int32  -> genBoundedIntegral
    Int64  -> genBoundedIntegral
    Word8  -> genBoundedIntegral
    Word16 -> genBoundedIntegral
    Word32 -> genBoundedIntegral
    Word64 -> genBoundedIntegral
    Float  -> genFractional
    Double -> genFractional

  where

  genBool :: Gen Bool
  genBool = do
    g <- stdGen
    return $ fst (random g)

  genBoundedIntegral :: (Bounded a, Integral a) => Gen a
  genBoundedIntegral = do
    let mn = minBound
        mx = maxBound `asTypeOf` mn
    n <- choose (toInteger mn, toInteger mx)
    return (fromInteger n `asTypeOf` mn)

  genFractional :: (Random a, Fractional a) => Gen a
  genFractional = do
    g <- stdGen
    return $ fst (random g)

--------------------------------------------------------------------------------

-- Given an int i and type t, make a list of length i containing random values
-- over the type.
randomReplicate :: Int -> Type a -> Gen [a]
randomReplicate i t = mapM (\_ -> randomFromType t) [1..i]

--------------------------------------------------------------------------------

choose :: Random a => (a, a) -> Gen a
choose rng = do
  g <- stdGen
  return $ fst (randomR rng g)

oneOf :: [Gen a] -> Gen a
oneOf [] = impossible "oneof" "copilot-core" 
oneOf gs = choose (0,length gs - 1) >>= (gs !!)

-- | Takes a list of pairs (weight, Gen), and choose the Gen based on the
-- weights.  To get the frequency of choosing a Gen, sum up all the weights, and
-- choose c between 1 and the total.  Now recurse down the list, choosing an
-- item only when c <= weight.  If not, subtract the current weight from c.
freq :: [(Int, Gen a)] -> Gen a
freq [] = impossible "feq" "copilot-core" 
freq xs0 = choose (1, tot) >>= (`pick` xs0)
  where
  tot = sum (map fst xs0)
  pick n ((k,x):xs)
    | n <= k    = x
    | otherwise = pick (n-k) xs
  pick _ _  = impossible "pick" "copilot-core" 

elements :: [a] -> Gen a
elements [] = impossible "elements" "copilot-core" 
elements xs = (xs !!) `fmap` choose (0, length xs - 1)

--------------------------------------------------------------------------------
