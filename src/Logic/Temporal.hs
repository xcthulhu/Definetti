{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE TypeSynonymInstances  #-}

module Logic.Temporal where

import           Control.Monad            (MonadPlus)
import qualified Data.Set

import           Logic.Propositional      (Propositional ((:&&:), Not, Verum))
import           Logic.Propositional.DPLL (ConstrainedModelSearch,
                                           Literal (Neg, Pos), ModelSearch,
                                           findConstrainedModel, findModel)
-- TODO: Timestamps


data Temporal a = a `Until` a | Always a deriving (Ord, Show, Eq)

type TemporalCNF a = Data.Set.Set (Data.Set.Set (Temporal a))

instance ( Ord p
         , MonadPlus m
         , ConstrainedModelSearch d p m )
         => ModelSearch d (TemporalCNF (Propositional p)) m where
  findModel = undefined

instance ( Ord p
         , MonadPlus m
         , ConstrainedModelSearch d p m )
         => ConstrainedModelSearch d (Temporal (Propositional p)) m where
  findConstrainedModel = findModel . Data.Set.map toTemporalDisj where
    toTemporalDisj (Pos t) = Data.Set.singleton t
    toTemporalDisj (Neg (Always p)) =
        Data.Set.singleton (Verum `Until` Not p)
    toTemporalDisj (Neg (p `Until` q)) =
        Data.Set.fromList [ Always (Not q)
                          , p `Until` (Not p :&&: Not q)
                          ]
