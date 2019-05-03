{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MonoLocalBinds #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE TupleSections #-}

module Logic.Probability.Regression where

import Control.Arrow (second)
import Control.Monad (MonadPlus(mplus, mzero))
import Data.Foldable (fold)
import Data.List (sortOn)

import Logic.Propositional (Propositional)
import Logic.Propositional.Internal.DPLL (CNF)
import Logic.Propositional.Internal.Tseitin (tseitinTransform)
import Logic.Semantics (ConstrainedModelSearch, ModelSearch(findModel))

-- Inspired by the following powerset function implementation:
--
-- powerset :: Alternative f => [a] -> f [a]
-- powerset xs = powerset' xs []
--   where
--     powerset' :: Alternative f => [a] -> [a] -> f [a]
--     powerset' [] acc = pure acc
--     powerset' (x':xs') acc = powerset' xs' (x' : acc) <|> powerset' xs' acc

weightedMaxSatCNF ::
     (MonadPlus m, ModelSearch d (CNF a) m, Ord a, Num w, Ord w)
  => [(w, CNF a)]
  -> m d
weightedMaxSatCNF weightedCNFs =
  maybe mzero (pure . snd) =<<
  weightedMaxSat' (pure Nothing) (sortOn fst weightedCNFs) []
  where
    weight :: Num w => [(w, x)] -> w
    weight = foldr (\(w, _) currTotal -> w + currTotal) 0
    weightedMaxSat' ::
         (MonadPlus m, ModelSearch d (CNF a) m, Ord a, Num w, Ord w)
      => m (Maybe (w, d))
      -> [(w, CNF a)]
      -> [(w, CNF a)]
      -> m (Maybe (w, d))
    weightedMaxSat' currBest remaining acc =
      currBest >>= \case
        -- Skip branch if we've already found something better
        Just (w, _)
          | w >= (weight remaining + weight acc) -> currBest
        _
          | [] <- remaining ->
            (fmap (Just . (weight acc, )) . findModel . fold $ snd <$> acc) `mplus`
            currBest
        _
          | (x:xs) <- remaining ->
            weightedMaxSat' currBest xs (x : acc) `mplus`
            weightedMaxSat' currBest xs acc

weightedMaxSat ::
     (MonadPlus m, ConstrainedModelSearch d a m, Ord a, Num w, Ord w)
  => [(w, Propositional a)]
  -> m d
weightedMaxSat weightedFormulae =
  weightedMaxSatCNF $ second tseitinTransform <$> weightedFormulae
