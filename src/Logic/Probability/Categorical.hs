{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MonoLocalBinds #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NamedFieldPuns #-}

module Logic.Probability.Categorical
  ( Categorical(unCategorical)
  , mkCategorical
  , mix
  , CategoricalException (..)
  ) where

import Control.Arrow (first)
import Control.Exception (Exception)
import Control.Monad (ap, liftM)
import Data.Foldable (toList)
import Data.List.NonEmpty (NonEmpty)
import Data.Monoid ((<>))
import Data.Typeable (Typeable)

-- | Categorical Distribution
--   An empirical distribution is a non-empty list of models
--   with non-negative rational weights that sum to 1
newtype Categorical d = Categorical
  { unCategorical :: NonEmpty (Rational, d)
  } deriving (Eq, Ord, Show)

instance Monad Categorical where
  return d = Categorical . return $ (1, d)
  (Categorical weightedData) >>= action =
    Categorical $ do
      (datumWeight, datum) <- weightedData
      (resultWeight, result) <- unCategorical $ action datum
      return (datumWeight * resultWeight, result)

instance Applicative Categorical where
  pure = return
  (<*>) = ap

instance Functor Categorical where
  fmap = liftM

data CategoricalException
  = NonPositiveCoefficients [Rational]
                            (NonEmpty Rational)
  | CoefficientsDoNotSumToOne (NonEmpty Rational)
  deriving (Eq, Ord, Show, Typeable)

instance Exception CategoricalException

-- | Smart constructor for categorical distributions
mkCategorical ::
     NonEmpty (Rational, d) -> Either CategoricalException (Categorical d)
mkCategorical weightedModels
  | any (<= 0) weights =
    let nonPositiveWeights = filter (<= 0) $ toList weights
     in Left $ NonPositiveCoefficients nonPositiveWeights weights
  | sum weights /= 1 = Left $ CoefficientsDoNotSumToOne weights
  | otherwise = Right $ Categorical weightedModels
  where
    weights = fst <$> weightedModels

-- | Mix two categorical ditributions
--
-- Let ᾶ = clamp α 0 1
-- effictively returns (1 - ᾶ) modelA + ᾶ model B
mix :: Rational -> Categorical d -> Categorical d -> Categorical d
mix alpha modelA@(Categorical wmsA) modelB@(Categorical wmsB)
  | alpha <= 0 = modelA
  | alpha >= 1 = modelB
  | otherwise =
    Categorical $ (first ((1 - alpha) *) <$> wmsA) <> (first (alpha *) <$> wmsB)
