{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MonoLocalBinds #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NamedFieldPuns #-}

module Logic.Probability.Inequalities
  ( ProbabilityInequality((:<), (:>), (:>=), (:<=))
  ) where


import Control.Applicative (Alternative, (<|>), empty)
import Control.Arrow ((***), first, second)
import Control.Monad (MonadPlus, msum)
import Data.Foldable (fold)
import Data.List (partition)
import qualified Data.Map as Map
import Data.Monoid ((<>))
import Data.Ratio (denominator)
import Data.Tuple (swap)

import Logic.Probability.Categorical
  ( Categorical
  , Probability((:*), (:+), (:-), Const, Pr)
  , pr
  )
import Logic.Propositional (Propositional(Not))
import Logic.Propositional.Internal.DPLL (CNF, ConstrainedModelSearch)
import Logic.Propositional.Internal.Tseitin (tseitinTransform)
import Logic.Semantics (ModelSearch(findModel), Semantics((|=)))

-- | Probability Inequalities
data ProbabilityInequality p
  = (Probability p) :< (Probability p)
  | (Probability p) :> (Probability p)
  | (Probability p) :>= (Probability p)
  | (Probability p) :<= (Probability p)
  deriving (Eq, Ord, Show)

instance Semantics d p =>
         Semantics (Categorical d) (ProbabilityInequality p) where
  m |= (a :< b) = pr m a < pr m b
  m |= (a :<= b) = pr m a <= pr m b
  m |= (a :>= b) = pr m a >= pr m b
  m |= (a :> b) = pr m a > pr m b

-- | Normal form for probabilistic inequalities / Trades
-- Represents equations of the form:
-- `w1 * a1 + w2 * a2 + ... + C </<= v1 * b1 + v2 * b2 + ...`
-- here `</<=` is either strict or non-strict inequality
data GTSummationNormalForm p = GTSummationNormalForm
  { leftHandTerms :: [(Rational, Propositional p)]
  , leftHandConstant :: Rational
  , rightHandTerms :: [(Rational, Propositional p)]
  , strict :: Bool
  }

plus :: (Ord p, Num n) => Map.Map p n -> Map.Map p n -> Map.Map p n
plus = Map.unionWith (+)

minus :: (Ord p, Num n) => Map.Map p n -> Map.Map p n -> Map.Map p n
x `minus` y = x `plus` Map.map negate y

extractPropositions ::
     Ord p => Probability p -> Map.Map (Propositional p) Rational
extractPropositions (Pr p) = Map.singleton p 1
extractPropositions (Const _) = Map.empty
extractPropositions (x :+ y) =
  extractPropositions x `plus` extractPropositions y
extractPropositions (x :- y) =
  extractPropositions x `minus` extractPropositions y
extractPropositions (a :* x) = Map.map (a *) (extractPropositions x)

extractConstantTerm :: Probability p -> Rational
extractConstantTerm (Pr _) = 0
extractConstantTerm (Const d) = d
extractConstantTerm (x :+ y) = extractConstantTerm x + extractConstantTerm y
extractConstantTerm (x :- y) = extractConstantTerm x - extractConstantTerm y
extractConstantTerm (a :* x) = a * extractConstantTerm x

normalizeProbInequality ::
     Ord p => ProbabilityInequality p -> GTSummationNormalForm p
normalizeProbInequality (b :> a) = normalizeProbInequality (a :< b)
normalizeProbInequality (b :>= a) = normalizeProbInequality (a :<= b)
normalizeProbInequality (a :< b) =
  (normalizeProbInequality (a :<= b)) {strict = True}
normalizeProbInequality (a :<= b) =
  GTSummationNormalForm
    { leftHandTerms = lhts
    , leftHandConstant = extractConstantTerm a - extractConstantTerm b
    , rightHandTerms = rhts
    , strict = False
    }
  where
    weightedTerms =
      fmap swap . Map.toList $
      extractPropositions a `minus` extractPropositions b
    (lhts, rhts) =
      second (fmap (first negate)) .
      partition ((> 0) . fst) . filter ((/= 0) . fst) $
      weightedTerms

unNormalizeProbInequality :: GTSummationNormalForm p -> ProbabilityInequality p
unNormalizeProbInequality gnf
  | GTSummationNormalForm lht lhConst rht True <- gnf =
    toProb lhConst lht :< toProb 0 rht
  | GTSummationNormalForm lht lhConst rht False <- gnf =
    toProb lhConst lht :<= toProb 0 rht
  where
    toProb c terms = foldr (:+) (Const c) $ (\(k, p) -> k :* Pr p) <$> terms

instance Semantics d p =>
         Semantics (Categorical d) (GTSummationNormalForm p) where
  m |= gnf = m |= unNormalizeProbInequality gnf

-- | Choose elements of a weighted collection with collective weight
--   greater than or equal to `k` such that if any element was removed
--   the collection would weigh less than `k`.
--
--   If all elements have weight 1, then
--   `|totalWeight choose k| = totalWeight! / (k!(totalWeight-k)!)`
--
--   Lifted into an arbitrary `Alternative` functor;
--   using `List` results in a list of all of the possibilities.
weightedChoose :: Alternative f => Integer -> [(Integer, a)] -> f [a]
weightedChoose k xs = weightedChoose' k xs (sum . fmap fst $ xs)
  where
    weightedChoose' ::
         Alternative f => Integer -> [(Integer, a)] -> Integer -> f [a]
    weightedChoose' c clauses totalWeight
      | c > totalWeight = empty
      | c <= 0 = pure []
      | [] <- clauses = error "Pattern should be unreachable!"
      | ((weight, x):clauses') <- clauses =
        let totalWeight' = totalWeight - weight
         in weightedChoose' c clauses' totalWeight' <|>
            fmap (x :) (weightedChoose' (c - weight) clauses' totalWeight')

-- | Find a model of some model of a group of weighted clauses
--   in conjunctive normal form with weight greater than `k`
weightedSatGT ::
     (Ord a, MonadPlus m, ModelSearch d (CNF a) m)
  => Integer
  -> [(Integer, CNF a)]
  -> m d
weightedSatGT k clauses = msum . fmap (findModel . fold) $ chooseN clauses
  where
    chooseN :: [(Integer, CNF a)] -> [[CNF a]]
    chooseN = weightedChoose (k + 1)

-- | Model search for probabilistic inequalities in
--   'GTSummationNormalForm'
--
--   This makes use of the law
--
--   ∃ P ∈ Probabilities . (∑cᵢ·P(ϕᵢ)) + A ≤ (∑kⱼ·P(ψⱼ)) + B
--                           ≡
--   IntegerWeightedMaxSat([(cᵢ·M, ¬ϕᵢ)] <> [(kⱼ·M, ψⱼ)]) > K
--
-- where
--   - M is the least common multiple of all of the cᵢ and kⱼ.
--   - K = ⌊(∑cᵢ + A - B )·M⌋ + 1
--
-- It is not necessary to solve IntegerWeightedMaxSat.
-- It is sufficient to find some model with weight exceeding K.
-- For that implies all IntegerWeightedMaxSat solutions
-- are greater than K.
--
-- findModel returns a model of clauses with weight greater than K
-- if possible.
instance (Ord p, MonadPlus m, ConstrainedModelSearch d p m) =>
         ModelSearch (Categorical d) (GTSummationNormalForm p) m where
  findModel GTSummationNormalForm { leftHandTerms
                                  , rightHandTerms
                                  , leftHandConstant
                                  , strict
                                  } = pure <$> weightedSatGT k clauses
    where
      allTerms = leftHandTerms <> rightHandTerms
      listLCM = foldr lcm 1
      m = fromIntegral . listLCM . fmap (denominator . fst) $ allTerms
      transform = (floor . (m *)) *** tseitinTransform
      transformedLeftHandSide = transform . second Not <$> leftHandTerms
      transformedRightHandSide = transform <$> rightHandTerms
      clauses = transformedLeftHandSide <> transformedRightHandSide
      k =
        floor
          ((fromIntegral . sum . fmap fst) transformedLeftHandSide +
           m * leftHandConstant) +
        if strict
          then 0
          else 1

instance (Ord p, MonadPlus m, ConstrainedModelSearch d p m) =>
         ModelSearch (Categorical d) (ProbabilityInequality p) m where
  findModel = findModel . normalizeProbInequality
