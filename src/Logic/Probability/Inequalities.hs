{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NamedFieldPuns #-}

module Logic.Probability.Inequalities
  ( ProbabilityInequality((:<), (:>), (:>=), (:<=))
  ) where

import Control.Arrow ((***), first, second)
import Control.Monad (MonadPlus)
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
import Logic.Propositional.Internal.DPLL (ConstrainedModelSearch)
import Logic.Propositional.Internal.Tseitin (tseitinTransform)
import Logic.Propositional.Internal.WeightedSat (intWeightedSatGT)
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

-- | Model search for probabilistic inequalities in
--   'GTSummationNormalForm'
--
--   This makes use of the law:
--
--   ∃ P ∈ Probabilities . (∑cᵢ·P(ϕᵢ)) + A ≤ (∑kⱼ·P(ψⱼ)) + B
--                           ≡
--   |intWeightedMaxSat ([(cᵢ·M, ¬ϕᵢ)] <> [(kⱼ·M, ψⱼ)])| > K + 1
--
-- where
--   - M is the least common multiple of all of the cᵢ and kⱼ.
--   - K = ⌊(∑cᵢ + A - B )·M⌋
--
-- There is a similar law for strict inequality:
--
--   ∃ P ∈ Probabilities . ∑(cᵢ·P(ϕᵢ)) + A < ∑(kⱼ·P(ψⱼ)) + B
--                           ≡
--   |intWeightedMaxSat ([(cᵢ·M, ¬ϕᵢ)] <> [(kⱼ·M, ψⱼ)])| > K
--
-- It is not necessary to solve intWeightedMaxSat.
-- It is sufficient to find some model with weight exceeding K.
-- For that implies all intWeightedMaxSat solutions have weight
-- greater than K.
--
-- This yields the law:
--
--   k < |intMaxSAT weightedClauses| ≡ intWeightedSatGT k weightedClauses
--
--
-- findModel returns a model of clauses with weight greater than K
-- if possible.
instance (Ord p, MonadPlus m, ConstrainedModelSearch d p m) =>
         ModelSearch (Categorical d) (GTSummationNormalForm p) m where
  findModel GTSummationNormalForm { leftHandTerms
                                  , rightHandTerms
                                  , leftHandConstant
                                  , strict
                                  } = pure <$> intWeightedSatGT k clauses
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
