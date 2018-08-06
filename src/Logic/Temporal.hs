{-# LANGUAGE DeriveFunctor         #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RecordWildCards       #-}
{-# LANGUAGE TupleSections         #-}

module Logic.Temporal (Temporal (Until, Always), before) where

import           Control.Monad               (MonadPlus, msum)
import           Data.List                   (permutations)
import           Data.List.NonEmpty          (NonEmpty ((:|)), reverse, scanl)
import           Data.Monoid                 (mempty, (<>))
import qualified Data.Set
import           Data.Traversable            (sequence)
import           Prelude                     hiding (reverse, scanl, sequence)

import           Logic.Propositional         (Propositional ((:&&:), Not, Proposition, Verum))
import           Logic.Propositional.DPLL    (CNF, ConstrainedModelSearch,
                                              Literal (Neg, Pos), ModelSearch,
                                              findConstrainedModel, findModel)
import           Logic.Propositional.Tseitin (Definitional, tseitinTransform)
import           Logic.Semantics             (Semantics, (|=))

-- | Temporal logic primitives
data Temporal a = a `Until` a | Always a deriving (Ord, Show, Eq, Functor)

-- Expression for `before` operator based on temporal logic primitives
before :: Propositional p
       -> Propositional p
       -> Propositional (Temporal (Propositional p))
a `before` b = Proposition (Not b `Until` a) :&&:
               Proposition (Verum `Until` b)

data Until_ a = a `Until_` a deriving (Functor)

instance Semantics d p => Semantics (NonEmpty d) (Temporal p) where
  (|=) (m:|ms) = (|==) (m:ms) where
    ms'      |== (Always p)      = all (|= p) ms'
    (m':ms') |== u@(p `Until` q) = m' |= q || (m' |= p && ms' |== u)
    []       |== (_ `Until` _)   = False

data TimelineProblem p = TimelineProblem
  { always        :: CNF (Definitional p)
  , untilTimeline :: [Until_ (CNF (Definitional p))]
  }

instance ( Ord p
         , MonadPlus m
         , ConstrainedModelSearch d p m )
         => ModelSearch (NonEmpty d) (TimelineProblem p) m where
  findModel TimelineProblem {..} =
      fmap (reverse . fmap snd) . sequence
    $ scanl findTimeStepModel initialState untilTimeline where
      initialState = (always,) <$> findModel always
      findTimeStepModel state (p `Until_` q) = do
        (always', _) <- state
        (always' <> p,) <$> findModel (always' <> q)

data PreTimeline p = PreTimeline
  { preAlways :: CNF (Definitional p)
  , preUntils :: [Until_ (CNF (Definitional p))]
  , choices   :: [[Temporal (CNF (Definitional p))]]
  }

instance ( Ord p
         , MonadPlus m
         , ConstrainedModelSearch d p m )
         => ConstrainedModelSearch (NonEmpty d) (Temporal (Propositional p)) m where
  findConstrainedModel clauses = searchTimelines preTimeline where
    preTimeline = foldr preproc (PreTimeline mempty [] [])
                . Data.Set.toList
                $ clauses
    addTemp pt@PreTimeline{..} (Always a) =
      pt { preAlways = preAlways <> a}
    addTemp pt@PreTimeline{..} (p `Until` q) =
      pt { preUntils = (p `Until_` q) : preUntils }
    addTempT pt = addTemp pt . fmap tseitinTransform
    preproc (Pos p@(Always _)) pt = addTempT pt p
    preproc (Pos u@(_ `Until` _)) pt = addTempT pt u
    preproc (Neg (Always p)) pt = addTempT pt (Verum `Until` Not p)
    preproc (Neg (p `Until` q)) pt@PreTimeline{..} =
      pt { choices = (fmap . fmap) tseitinTransform
                     [p `Until` (Not p :&&: Not q), Always (Not q)]
                   : choices
         }
    searchTimelines pt@PreTimeline {..} = case choices of
      []     -> msum (    findModel . TimelineProblem preAlways
                      <$> permutations preUntils )
      (c:cs) -> msum (searchTimelines . addTemp (pt {choices = cs}) <$> c)
