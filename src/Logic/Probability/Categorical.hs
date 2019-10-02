module Logic.Probability.Categorical
  ( Categorical(unCategorical)
  , mkCategorical
  , mix
  , CategoricalException(..)
  , Probability(Pr, Const, (:+), (:*), (:-))
  , pr
  , dirac
  ) where

import Control.Exception (Exception)
import Data.Foldable (toList)
import Data.List.NonEmpty (NonEmpty)
import qualified Data.Map as Map
import Data.Typeable (Typeable)
import Data.Tuple (swap)

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
  { unCategorical :: Map.Map d Rational
  } deriving (Eq, Ord, Show)

data CategoricalException
  = NonPositiveCoefficients [Rational]
                            (NonEmpty Rational)
  | CoefficientsDoNotSumToOne (NonEmpty Rational)
  deriving (Eq, Ord, Show, Typeable)

instance Exception CategoricalException

dirac :: Ord d => d -> Categorical d
dirac d = Categorical $ Map.fromList [(d,1)]

-- | Smart constructor for categorical distributions
mkCategorical ::
     Ord d
  => NonEmpty (Rational, d)
  -> Either CategoricalException (Categorical d)
mkCategorical weightedModels
  | any (<= 0) weights =
    let nonPositiveWeights = filter (<= 0) $ toList weights
     in Left $ NonPositiveCoefficients nonPositiveWeights weights
  | sum weights /= 1 = Left $ CoefficientsDoNotSumToOne weights
  | otherwise =
    Right . Categorical . Map.fromList . toList $ swap <$> weightedModels
  where
    weights = fst <$> weightedModels

-- | Mix two categorical ditributions
--
-- Let ᾶ = clamp α 0 1
-- effictively returns (1 - ᾶ) modelA + ᾶ model B
mix :: Ord d => Rational -> Categorical d -> Categorical d -> Categorical d
mix alpha modelA@(Categorical wmsA) modelB@(Categorical wmsB)
  | alpha <= 0 = modelA
  | alpha >= 1 = modelB
  | otherwise =
    let wmsA' = Map.map ((1 - alpha) *) wmsA
        wmsB' = Map.map (alpha *) wmsB
     in Categorical $ Map.unionWith (+) wmsA' wmsB'

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
  sum [coeff | (model, coeff) <- Map.toList $ unCategorical m, model |= p]
