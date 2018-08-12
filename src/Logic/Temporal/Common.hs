{-# LANGUAGE DeriveFunctor         #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RecordWildCards       #-}

module Logic.Temporal.Common (Temporal (Until, Always), before, until, Until_ (Until_), TimelineProblem (TimelineProblem, always, untils)) where

import           Control.Applicative         (Alternative ((<|>)))
import           Control.Monad               (MonadPlus, msum)
import           Data.List.NonEmpty          (NonEmpty ((:|)), reverse)
import           Data.Monoid                 (mempty, (<>))
import qualified Data.Set
import           Prelude                     hiding (reverse, until)

import           Logic.Propositional         (Literal (Neg, Pos), Propositional ((:&&:), Not, Proposition, Verum))
import           Logic.Propositional.DPLL    (CNF, ConstrainedModelSearch (findConstrainedModel),
                                              ModelSearch (findModel))
import           Logic.Propositional.Tseitin (Definitional, tseitinTransform)
import           Logic.Semantics             (Semantics, (|=))


-- | Temporal logic primitives
data Temporal p = p `Until` p | Always p deriving (Ord, Show, Eq, Functor)

until :: Propositional p
       -> Propositional p
       -> Propositional (Temporal (Propositional p))
a `until` b = Proposition (a `Until` b)

-- Expression for `before` operator based on temporal logic primitives
before :: Propositional p
       -> Propositional p
       -> Propositional (Temporal (Propositional p))
a `before` b = (Not b `until` a) :&&: (Verum `until` b)

-- Models for Temporal literals are NonEmpty sequences of models
-- for some sublogic
instance Semantics d p => Semantics (NonEmpty d) (Temporal p) where
  (|=) (m:|ms) = (|==) (m:ms) where
    ms'      |== (Always p)      = all (|= p) ms'
    (m':ms') |== u@(p `Until` q) = m' |= q || (m' |= p && ms' |== u)
    []       |== (_ `Until` _)   = False

-- Primitive for just `Until_` literals used in model search
data Until_ a = a `Until_` a deriving (Functor)

data TimelineProblem p = TimelineProblem
  { always :: CNF (Definitional p)
  , untils :: [Until_ (CNF (Definitional p))]
  }

pickOne :: [a] -> [(a,[a])]
pickOne []     = []
pickOne [x]    = [(x,[])]
pickOne (x:xs) = (x,xs) : [(y,x:ys) | (y,ys) <- pickOne xs]

-- Model search for TimelineProblems involves checking every
-- permutation of the `Until_` literals associated with that problem.
-- For each permutation, literals are treated as reverse chronological
-- order and a model is constructed as such.
-- We use `pickOne` so we can pick one literal at a time and early exit.
instance ( Ord p
         , MonadPlus m
         , ConstrainedModelSearch d p m )
         => ModelSearch (NonEmpty d) (TimelineProblem p) m where
  findModel TimelineProblem {..} =
    reverse <$> ((:|) <$> initialState <*> search always untils) where
      initialState           = findModel always
      search _ []            = pure mempty
      search always' untils' = msum $ tryTimeline always' <$> pickOne untils'
      tryTimeline always' (p `Until_` q, untils') = do
        t <- findModel (always' <> q)
        ts <- search (always' <> p) untils'
        pure (t:ts)

{-------------------------- Slow Model Search Routine -------------------------}

-- This model search routine is exponentially slower than the one in
-- Optimized.hs. It also repeatedly performs the Tseitin transformation.
-- However, that one is *less general* and will not work flexibly when called by
-- other Answer-SAT solvers

data Choice p = Choice p p deriving Functor

choose :: Alternative f => Choice (f a) -> f a
choose (Choice p q) = p <|> q

data PreTimeline p = PreTimeline
  { preAlways :: CNF (Definitional p)
  , preUntils :: [Until_ (CNF (Definitional p))]
  , choices   :: [Choice (Temporal (CNF (Definitional p)))]
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
                     (Choice (p `Until` (Not p :&&: Not q)) (Always (Not q)))
                   : choices
         }
    searchTimelines pt@PreTimeline {..} = case choices of
      []     -> findModel (TimelineProblem preAlways preUntils)
      (c:cs) -> choose (searchTimelines . addTemp (pt {choices = cs}) <$> c)
