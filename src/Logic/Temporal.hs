{-# LANGUAGE DeriveFunctor         #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RecordWildCards       #-}

module Logic.Temporal (Temporal (Until, Always), before, until, TemporalFormula (TemporalFormula), PositiveTemporal) where

import           Control.Applicative         (Alternative ((<|>)))
import           Control.Monad               (MonadPlus, msum)
import           Data.Foldable               (foldMap)
import           Data.List.NonEmpty          (NonEmpty ((:|)), reverse)
import           Data.Monoid                 (mempty, (<>))
import qualified Data.Set
import           Prelude                     hiding (reverse, until)

import           Logic.Propositional         (FreeModel, FreeVars (Bound, Free), Propositional ((:&&:), Not, Proposition, Verum))
import           Logic.Propositional.DPLL    (CNF, ConstrainedModelSearch (findConstrainedModel),
                                              Literal (Neg, Pos),
                                              ModelSearch (findModel))
import           Logic.Propositional.Tseitin (Definitional,
                                              Definitional' (Atom, Definition),
                                              tseitinTransform)
import           Logic.Semantics             (Semantics, (|=))

-- | Temporal logic primitives
data Temporal p = p `Until` p | Always p deriving (Ord, Show, Eq, Functor)

-- Temporal logic solver turns all temporal logic literals positive
-- This type in the internal API provides soft enforcement of this
newtype PositiveTemporal p =
  PositiveTemporal (Temporal (CNF (Definitional p))) deriving (Ord, Show, Eq)

newtype TemporalFormula v p =
  TemporalFormula (Propositional (FreeVars v (Temporal p))) deriving (Ord, Show, Eq)

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

data TimelineProblem p = TimelineProblem
  { always :: CNF (Definitional p)
  , untils :: [Until_ (CNF (Definitional p))]
  }

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

instance Semantics d p => Semantics (NonEmpty d) (Temporal p) where
  (|=) (m:|ms) = (|==) (m:ms) where
    ms'      |== (Always p)      = all (|= p) ms'
    (m':ms') |== u@(p `Until` q) = m' |= q || (m' |= p && ms' |== u)
    []       |== (_ `Until` _)   = False



pickOne :: [a] -> [(a,[a])]
pickOne []     = []
pickOne [x]    = [(x,[])]
pickOne (x:xs) = (x,xs) : [(y,x:ys) | (y,ys) <- pickOne xs]

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
