{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MonoLocalBinds        #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE UndecidableInstances  #-}

module Logic.Probability
  ( Probability (..)
  , ProbabilityInequality (..)
  ) where

import           Control.Applicative         (empty, pure)
import           Control.Monad               (MonadPlus, msum)
import qualified Data.Foldable               (fold)
import           Data.Ratio                  (denominator)
import           Logic.Propositional         (Propositional (Not))
import           Logic.Propositional.DPLL    (CNF, Clause, ConjClause)
import           Logic.Propositional.Tseitin (Definitional, tseitinTransform)
import           Logic.Semantics             (ModelSearch (findModel),
                                              Semantics ((|=)))

-- | Probability Inequalities

data Probability p = Pr (Propositional p)
                   | Const Rational
                   | (Probability p) :+ (Probability p)
                   deriving (Ord, Show, Eq)

data ProbabilityInequality p = (Probability p) :<  (Probability p)
                             | (Probability p) :>  (Probability p)
                             | (Probability p) :>= (Probability p)
                             | (Probability p) :<= (Probability p)
                             deriving (Ord, Show, Eq)

evalProbability :: Semantics model (Clause p) => model -> Probability p -> Rational
evalProbability _ (Const c) = c
evalProbability m (Pr p)    = if m |= p then 1 else 0
evalProbability m (x :+ y)  = evalProbability m x + evalProbability m y

instance Semantics model (Clause p) =>
         Semantics model (ProbabilityInequality p) where
  m |= (a :< b)  = evalProbability m a <  evalProbability m b
  m |= (a :<= b) = evalProbability m a <= evalProbability m b
  m |= (a :>= b) = evalProbability m a >= evalProbability m b
  m |= (a :> b)  = evalProbability m a >  evalProbability m b

extractPropositions :: Probability p -> [Propositional p]
extractPropositions (Pr    p) = [p]
extractPropositions (Const _) = []
extractPropositions (x:+y   ) = extractPropositions x ++ extractPropositions y

extractConstantTerm :: Probability p -> Rational
extractConstantTerm (Pr    _) = 0
extractConstantTerm (Const d) = d
extractConstantTerm (x:+y   ) = extractConstantTerm x + extractConstantTerm y

maxSatNComponents :: Ord p
                  => Probability p
                  -> Probability p
                  -> (Rational, [CNF (Definitional p)])
maxSatNComponents leftHandSide rightHandSide = (k, clauses)
  where
    leftHandPropositions = extractPropositions leftHandSide
    rightHandPropositions = extractPropositions rightHandSide
    clauses = fmap tseitinTransform
                   (fmap Not rightHandPropositions ++ leftHandPropositions)
    k =   fromIntegral (length rightHandPropositions)
        + extractConstantTerm rightHandSide
        - extractConstantTerm leftHandSide

-- https://mail.haskell.org/pipermail/haskell-cafe/2003-June/004484.html
(/\/)        :: [a] -> [a] -> [a]
[]     /\/ ys = ys
(x:xs) /\/ ys = x : (ys /\/ xs)

-- | Choose `k` elements of a collection of `n` items
--   Results in `n choose k = n! / (k!(n-k)!)`
--   Lifted into an `Alternative` functor (so DList may be used)
choose :: [a] -> Int -> Int -> [[a]]
choose clauses n k
  | k > n             = empty
  | k <= 0            = pure []
  | k == n            = pure clauses
  | [] <- clauses     = error "This should never happen"
  | (x:xs) <- clauses = choose xs n' k /\/ fmap (x :) (choose xs n' (k - 1))
  where n' = n - 1

-- | Determine if the largest sublist of CNFs simultaneously satisfiable
--   has length no bigger than `n`
maxSatN
  :: (Ord a, MonadPlus m, ModelSearch m model (CNF a))
  => Int
  -> [CNF a]
  -> m model
maxSatN k = msum . fmap (findModel . Data.Foldable.fold) . chooseN
 where
   chooseN xs = choose xs (length xs) (k + 1)

instance ( Ord p
         , MonadPlus m
         , ModelSearch m model (ConjClause p) )
         => ModelSearch m model (ProbabilityInequality p)
  where
    findModel (a :<= b) = findModel (b :>= a)
    findModel (a :< b)  = findModel (b :> a)
    findModel (b :>= a) = maxSatN k' clauses
      where
        (k, clauses) = maxSatNComponents b a
        -- If a Rational is of the form (x / 1), it is an integer
        k' = ceiling (if 1 == denominator k then k + 1 else k)
    findModel (b :> a)  = maxSatN (floor k) clauses
      where
        (k, clauses) = maxSatNComponents b a
