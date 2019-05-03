{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MonoLocalBinds #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NamedFieldPuns #-}

module Logic.Probability.Categorical
  ( Categorical(unCategorical)
  , mkCategorical
  , mix
  , CategoricalException(..)
  , Probability(Pr, Const, (:+), (:*), (:-))
  , pr
  ) where

import Control.Arrow (first)
import Control.Exception (Exception)
import Control.Monad (ap, liftM)
import Data.Foldable (toList)
import Data.List.NonEmpty (NonEmpty)
import Data.Monoid ((<>))
import Data.Typeable (Typeable)

import Logic.Propositional (Propositional)
import Logic.Semantics (Semantics((|=)))

{- ---------------------- Categorical Distributions ------------------------ -}
-- | Categorical Distributions
--
--   A categorical distribution is a non-empty list of models
--   with positive rational weights that sum to 1
--
--   Constructor is not exposed, use smart constructors
--
--   This can be thought of as a convex combination of models
--
--   This is essentially Nils Nilsson's "Π" representation of
--   probability measures which may be found in "Probabilistic Logic" (1986)
--   http://ai.stanford.edu/~nilsson/OnlinePubs-Nils/PublishedPapers/problogic.pdf
newtype Categorical d = Categorical
  { unCategorical :: NonEmpty (Rational, d)
  } deriving (Eq, Ord, Show)

-- | Categorical distributions form a monad
--
--   Inspired by Eric Kidd's "Refactoring Probability Distributions, Part 1" (2006)
--   https://web.archive.org/web/20181212000543/http://www.randomhacks.net/2007/02/21/refactoring-probability-distributions/
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

{- ------------------------- Probability Calculus -------------------------- -}
data Probability p
  = Pr (Propositional p)
  | Const Rational
  | (Probability p) :+ (Probability p)
  | (Probability p) :- (Probability p)
  | Rational :* (Probability p)
  deriving (Eq, Ord, Show)

-- | Convert a categorical distribution over models into a probability measure
--
--   Obeys the axioms for a finitely additive measure (ie, the "Kolmogorov Axioms"):
--
--   1. ∀ ɸ m . pr m ɸ ≥ 0
--   2. ∀ ɸ . If (∀ m . m |= ɸ) then (∀ n . pr n ɸ = 1)
--   3. ∀ ɸ ψ . If (∀ m . not (m |= ɸ ∧ ψ)) then (∀ n . pr n (ɸ ∨ ψ) = (pr n ɸ) + (pr n ψ)))
--
--   Brian Weatherson provides a simpler alternative to axiom 3 in
--   "From Classical to Intuitionistic Probability" (2003)
--   http://brian.weatherson.org/conprob.pdf
--
--   3'. ∀ ɸ ψ m . (pr m ɸ) + (pr m ψ) = (pr m (ɸ ∧ ψ)) + (pr m (ɸ ∨ ψ))
pr :: Semantics d p => Categorical d -> Probability p -> Rational
pr _ (Const c) = c
pr m (x :+ y) = pr m x + pr m y
pr m (x :- y) = pr m x - pr m y
pr m (a :* x) = a * pr m x
pr m (Pr p) =
  sum [coeff | (coeff, model) <- toList $ unCategorical m, model |= p]
