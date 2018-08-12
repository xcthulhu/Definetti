{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RecordWildCards       #-}

module Logic.Temporal.Optimized (TemporalFormula (TemporalFormula), PositiveTemporal) where

import           Control.Monad               (MonadPlus)
import           Data.Foldable               (foldMap)
import           Data.List.NonEmpty          (NonEmpty)
import           Data.Monoid                 (mempty, (<>))
import qualified Data.Set

import           Logic.Propositional         (FreeModel, FreeVars (Bound, Free),
                                              Propositional ((:&&:), Not, Verum))
import           Logic.Propositional.DPLL    (CNF, ConstrainedModelSearch (findConstrainedModel),
                                              Literal (Neg, Pos),
                                              ModelSearch (findModel))
import           Logic.Propositional.Tseitin (Definitional,
                                              Definitional' (Atom, Definition),
                                              tseitinTransform)
import           Logic.Semantics             (Semantics, (|=))
import           Logic.Temporal.Common       (Temporal (Always, Until), TimelineProblem (TimelineProblem, always, untils),
                                              Until_ (Until_))

-- Temporal logic solver turns all temporal logic literals positive
-- This type in the internal API provides soft enforcement of this
newtype PositiveTemporal p =
  PositiveTemporal (Temporal (CNF (Definitional p))) deriving (Ord, Show, Eq)

newtype TemporalFormula v p =
  TemporalFormula (Propositional (FreeVars v (Temporal p))) deriving (Ord, Show, Eq)

instance ( Ord v
         , Semantics d p )
         => Semantics (FreeModel v (NonEmpty d))
                      (TemporalFormula v (Propositional p)) where
  m |= (TemporalFormula p) = m |= p

instance ( Ord p
         , MonadPlus m
         , ConstrainedModelSearch d p m)
         => ConstrainedModelSearch (NonEmpty d)
                                   (PositiveTemporal p)
                                   m
  where
    findConstrainedModel clause =
      findModel (foldr addTemp initTLP clause) where
        initTLP = TimelineProblem mempty mempty
        addTemp (Pos (PositiveTemporal (p `Until` q)))
                tlp@TimelineProblem {..} =
                  tlp {untils = p `Until_` q : untils}
        addTemp (Pos (PositiveTemporal (Always a)))
                tlp@TimelineProblem {..} = tlp {always = a <> always}
        addTemp (Neg _) _ = error "PositiveTemporal literals must be positive"


instance ( Ord v
         , Ord p
         , MonadPlus m
         , ConstrainedModelSearch d p m )
         => ModelSearch (FreeModel v (NonEmpty d))
                        (TemporalFormula v (Propositional p))
                        m
  where
    findModel (TemporalFormula f) = findModel f' where
      f' = ((Data.Set.map . foldMap) transform . tseitinTransform) f
      mkLit constructor =
          Data.Set.singleton
        . constructor
        . (fmap . fmap) (PositiveTemporal . fmap tseitinTransform)
      mkTempLit = mkLit Pos . Atom . Bound
      transform (Pos q)                 = mkLit Pos q
      transform (Neg q@(Definition _))  = mkLit Neg q
      transform (Neg q@(Atom (Free _))) = mkLit Neg q
      transform (Neg (Atom (Bound (Always a)))) =
        mkTempLit (Verum `Until` Not a)
      transform (Neg (Atom (Bound (q `Until` r)))) =
        mkTempLit (q `Until` (Not q :&&: Not r)) <> mkTempLit (Always (Not r))
