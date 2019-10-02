{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NamedFieldPuns #-}

module Logic.Temporal
  ( Temporal(Until, Always)
  , before
  , until
  ) where

import Control.Applicative (Alternative((<|>)))
import Control.Arrow (first, second)
import Control.Monad (MonadPlus, msum)
import qualified Data.Foldable (fold)
import Data.List.NonEmpty (NonEmpty((:|)), reverse)
import Data.Monoid (Monoid, mappend, mempty)
import Data.Semigroup (Semigroup, (<>))
import qualified Data.Set
import Prelude hiding (reverse, until)

import Logic.Propositional (Propositional((:&&:), Not, Proposition, Verum))
import Logic.Propositional.Internal.DPLL
  ( CNF
  , ConstrainedModelSearch(findConstrainedModel)
  , Literal(Neg, Pos)
  , ModelSearch(findModel)
  )
import Logic.Propositional.Internal.Tseitin (Definitional, tseitinTransform)
import Logic.Semantics (Semantics, (|=))

-- | Simplified linear temporal logic primitives
--
--   Terms of 'Propositional (Temporal p)' are a sublanguage of traditional
--   linear temporal logic.
--
--   However, this sublanguage corresponds to linear temporal logic without
--   nested modalities.
--
--   One benefit of this simplified language is that it is composable with other
--   inference systems in our Answer-SAT framework.
data Temporal p
  = Until p
          p
  | Always p
  deriving (Ord, Show, Eq, Functor)

until ::
     Propositional p
  -> Propositional p
  -> Propositional (Temporal (Propositional p))
a `until` b = Proposition (a `Until` b)

-- Expression for `before` operator based on temporal logic primitives
before ::
     Propositional p
  -> Propositional p
  -> Propositional (Temporal (Propositional p))
a `before` b = Not b `until` (Not b :&&: a)

-- Used in decision algorithm
data Until_ a =
  Until_ a
         a
  deriving (Functor)

instance Semantics d p => Semantics (NonEmpty d) (Temporal p) where
  (|=) (m :| ms) = (|==) (m : ms)
    where
      ms' |== (Always p) = all (|= p) ms'
      (m':ms') |== u@(p `Until` q) = m' |= q || (m' |= p && ms' |== u)
      [] |== (_ `Until` _) = False

instance Semigroup a => Semigroup (Until_ a) where
  (a `Until_` b) <> (c `Until_` d) = (a <> c) `Until_` (b <> d)

instance Monoid a => Monoid (Until_ a) where
  mempty = mempty `Until_` mempty
  (a `Until_` b) `mappend` (c `Until_` d) =
    (a `mappend` c) `Until_` (b `mappend` d)

-- TODO: Try DList here for performance
multiPick :: [a] -> [([a], [a])]
multiPick = filter (not . null . fst) . multiPick'
  where
    multiPick' [] = pure ([], [])
    multiPick' (x:xs) =
      let choices = multiPick' xs
       in (first (x :) <$> choices) <> (second (x :) <$> choices)

data TimelineProblem p = TimelineProblem
  { always :: CNF (Definitional p)
  , untils :: [Until_ (CNF (Definitional p))]
  }

instance Semantics d p => Semantics (NonEmpty d) (TimelineProblem p) where
  ms |= TimelineProblem {always, untils} =
    ms |= Always always && and ((\(Until_ p q) -> ms |= Until p q) <$> untils)

instance (Ord p, MonadPlus m, ConstrainedModelSearch d p m) =>
         ModelSearch (NonEmpty d) (TimelineProblem p) m where
  findModel TimelineProblem {always, untils} =
    reverse <$> ((:|) <$> initialState <*> search always untils)
    where
      initialState = findModel always
      search _ [] = pure []
      search always' untils' = msum $ tryTimeline always' <$> multiPick untils'
      tryTimeline always' (selection, rest) = do
        let (p `Until_` q) = Data.Foldable.fold selection
        t <- findModel (always' <> q)
        ts <- search (always' <> p) rest
        pure (t : ts)

data Choice p =
  Choice p
         p
  deriving (Functor)

choose :: Alternative f => Choice (f a) -> f a
choose (Choice p q) = p <|> q

data PreTimeline p = PreTimeline
  { preAlways :: CNF (Definitional p)
  , preUntils :: [Until_ (CNF (Definitional p))]
  , choices :: [Choice (Temporal (CNF (Definitional p)))]
  }

instance (Ord p, MonadPlus m, ConstrainedModelSearch d p m) =>
         ConstrainedModelSearch (NonEmpty d) (Temporal (Propositional p)) m where
  findConstrainedModel clauses = searchTimelines preTimeline
    where
      preTimeline =
        foldr preproc (PreTimeline mempty [] []) . Data.Set.toList $ clauses
      addTemp pt@PreTimeline {preAlways} (Always a) =
        pt {preAlways = preAlways <> a}
      addTemp pt@PreTimeline {preUntils} (p `Until` q) =
        pt {preUntils = (p `Until_` q) : preUntils}
      addTempT pt = addTemp pt . fmap tseitinTransform
      preproc (Pos p@(Always _)) pt = addTempT pt p
      preproc (Pos u@(_ `Until` _)) pt = addTempT pt u
      preproc (Neg (Always p)) pt = addTempT pt (Verum `Until` Not p)
      preproc (Neg (p `Until` q)) pt@PreTimeline {choices} =
        pt
          { choices =
              (fmap . fmap)
                tseitinTransform
                (Choice (p `Until` (Not p :&&: Not q)) (Always (Not q))) :
              choices
          }
      searchTimelines pt@PreTimeline {preAlways, preUntils, choices} =
        case choices of
          [] -> findModel (TimelineProblem preAlways preUntils)
          (c:cs) -> choose (searchTimelines . addTemp (pt {choices = cs}) <$> c)
