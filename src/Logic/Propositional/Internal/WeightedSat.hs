{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MonoLocalBinds #-}

module Logic.Propositional.Internal.WeightedSat
  ( intWeightedSatGTE
  , intWeightedSatGT
  ) where

import Control.Applicative (Alternative, (<|>), empty)
import Data.Foldable (fold, asum)

import Logic.Propositional.Internal.DPLL (CNF)
import Logic.Semantics (ModelSearch(findModel))

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

-- | Find a model of weighted clauses in conjunctive normal form
--   with weight greater or equal to than `k`
--
--   In particular we have the rule:
--
--   k ≤ |intMaxSAT weightedClauses| ≡ intWeightedSatGTE k weightedClauses
--
--   The right hand side is thought to be more tractable than the left hand side.
--
--   The left hand side is in MAXSAT.
--   The right hand side is in NP.
--   It is believed NP ⊊ MAXSAT.

intWeightedSatGTE ::
     (Ord a, Alternative m, ModelSearch d (CNF a) m)
  => Integer
  -> [(Integer, CNF a)]
  -> m d
intWeightedSatGTE k weightedClauses = asum . fmap (findModel . fold) $ chooseN weightedClauses
  where
    chooseN :: [(Integer, CNF a)] -> [[CNF a]]
    chooseN = weightedChoose k

-- | Find a model of of weighted clauses in conjunctive normal form
--   with weight greater than `k`
--
--   We have the rule:
--
--   k < |intMaxSAT weightedClauses| ≡ intWeightedSatGT k weightedClauses
--
intWeightedSatGT ::
     (Ord a, Alternative m, ModelSearch d (CNF a) m)
  => Integer
  -> [(Integer, CNF a)]
  -> m d
intWeightedSatGT k = intWeightedSatGTE (k+1)
