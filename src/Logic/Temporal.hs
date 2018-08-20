{-# LANGUAGE DeriveFunctor         #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RecordWildCards       #-}
{-# LANGUAGE TupleSections         #-}

module Logic.Temporal (Temporal (Until, Always), before, until) where

import           Control.Applicative         (Alternative ((<|>)))
import           Control.Arrow               (second)
import           Control.Monad               (MonadPlus, msum)
import           Data.List.NonEmpty          (NonEmpty ((:|)), reverse)
import           Data.Monoid                 (Monoid, mappend, mempty, (<>))
import qualified Data.Set
import           Prelude                     hiding (reverse, until)

import           Logic.Propositional         (Propositional ((:&&:), Not, Proposition, Verum))
import           Logic.Propositional.DPLL    (CNF, ConstrainedModelSearch (findConstrainedModel),
                                              Literal (Neg, Pos),
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

data Until_ a = a `Until_` a deriving (Functor)

instance Semantics d p => Semantics (NonEmpty d) (Temporal p) where
  (|=) (m:|ms) = (|==) (m:ms) where
    ms'      |== (Always p)      = all (|= p) ms'
    (m':ms') |== u@(p `Until` q) = m' |= q || (m' |= p && ms' |== u)
    []       |== (_ `Until` _)   = False

instance Monoid a => Monoid (Until_ a) where
  mempty = mempty `Until_` mempty
  (a `Until_` b) `mappend` (c `Until_` d) = (a <> c) `Until_` (b <> d)

singlePick :: [a] -> [(a,[a])]
singlePick []     = mempty
singlePick [x]    = pure (x,[])
singlePick (x:xs) = (x,xs) : (second (x:) <$> singlePick xs)

data TimelineProblem p = TimelineProblem
  { always :: CNF (Definitional p)
  , untils :: [Until_ (CNF (Definitional p))]
  }

instance ( Ord p
         , MonadPlus m
         , ConstrainedModelSearch d p m )
         => ModelSearch (NonEmpty d) (TimelineProblem p) m where
  findModel TimelineProblem {..} =
    reverse <$> ((:|) <$> initialState <*> search always untils) where
      initialState = findModel always
      search _ [] = pure mempty
      search always' untils' =
        msum [ tryNowAndLater id us =<< mkModel u
             | (u, us) <- singlePick untils' ] where
          mkModel u@(_ `Until_` q) = (u,) <$> findModel (q <> always')
          -- Below, we use a DList-type optimization for laters to avoid appending
          tryNowAndLater laters [] m = mkTimeline (laters []) m
          tryNowAndLater laters (u0:rest) m@(u,_) =
            tryNowAndLater ((u0:) . laters) rest m
            <|>
            do
              m' <- mkModel (u <> u0)
              mkTimeline (laters rest) m' <|> tryNowAndLater laters rest m'
          mkTimeline untils'' (p `Until_` _, t) =
            (t:) <$> search (always' <> p) untils''

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
