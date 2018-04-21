{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MonoLocalBinds        #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RecordWildCards       #-}
{-# LANGUAGE UndecidableInstances  #-}

module Logic.Probability
  ( Probability (..)
  , ProbabilityInequality (..)
  ) where

import           Control.Applicative         (Alternative, empty, pure, (<|>))
import           Control.Monad               (MonadPlus, msum)
import qualified Data.Foldable               (fold)
import           Data.Monoid                 ((<>))
import           Data.Ratio                  (denominator)
import           Logic.Propositional         (Propositional (Not))
import           Logic.Propositional.DPLL    (CNF, ConjClause)
import           Logic.Propositional.Tseitin (tseitinTransform)
import           Logic.Semantics             (ModelSearch (findModel),
                                              Semantics ((|=)))

-- | Probability Inequalities
data Probability p = Pr (Propositional p)
                   | Const Rational
                   | (Probability p) :+ (Probability p)
                   | Rational :* (Probability p)
                   deriving (Ord, Show, Eq)

data ProbabilityInequality p = (Probability p) :<  (Probability p)
                             | (Probability p) :>  (Probability p)
                             | (Probability p) :>= (Probability p)
                             | (Probability p) :<= (Probability p)
                             deriving (Ord, Show, Eq)

-- TODO: This is wrong, use probability functions
evalProbability :: Semantics model p
                => model
                -> Probability p
                -> Rational
evalProbability _ (Const c) = c
evalProbability m (Pr p)    = if m |= p then 1 else 0
evalProbability m (x :+ y)  = evalProbability m x + evalProbability m y
evalProbability m (a :* x)  = a * evalProbability m x

instance Semantics model p =>
         Semantics model (ProbabilityInequality p) where
  m |= (a :< b)  = evalProbability m a <  evalProbability m b
  m |= (a :<= b) = evalProbability m a <= evalProbability m b
  m |= (a :>= b) = evalProbability m a >= evalProbability m b
  m |= (a :> b)  = evalProbability m a >  evalProbability m b

-- | Choose `k` elements of a collection of weighted elements with
--   specified total weight. In the event that all elements have weight 1,
--   this results in exactly
--   `totalWeight choose k = totalWeight! / (k!(totalWeight-k)!)`
--   possible choices.
--   Lifted into an arbitrary `Alternative` functor;
--   using `List` results in a list of all of the possible choices.
weightedChoose :: Alternative f
               => [(Integer, a)]
               -> Integer
               -> Integer
               -> f [a]
weightedChoose clauses totalWeight k
  | k > totalWeight             = empty
  | k <= 0                      = pure []
  | k == totalWeight            = pure (map snd clauses)
  | [] <- clauses               = error "This should never happen"
  | ((weight, x):xs) <- clauses =
  let totalWeight' = totalWeight - weight
  in weightedChoose xs totalWeight' k <|>
     fmap (x :) (weightedChoose xs totalWeight' (k - weight))

-- | Normal form for probabilistic inequalities / Trades
-- Represents equations of the form:
-- `w1 * a1 + w2 * a2 + ... + C1 </<= v1 * b1 + v2 * b2 + .. + C2`
-- here `</<=` is either strict or non-strict inequality

data GTSummationNormalForm a =
  GTSummationNormalForm { leftHandTerms     :: [(Rational, a)]
                        , leftHandConstant  :: Rational
                        , rightHandTerms    :: [(Rational, a)]
                        , rightHandConstant :: Rational
                        , strict            :: Bool }

instance ( Ord p
         , MonadPlus m
         , ModelSearch m model (ConjClause p) )
         => ModelSearch m model (GTSummationNormalForm (Propositional p))
  where
    findModel GTSummationNormalForm {..} = maxSatN (floor k) clauses
      where
        denominatorProduct =
          fromIntegral (product (fmap (denominator . fst)
                                      (leftHandTerms <> rightHandTerms)))
        transform = fmap (\ (w, p) -> ( floor (denominatorProduct * w)
                                      , tseitinTransform p))
        transformedLeftHandSide = (transform . fmap (\ (w, p) -> (w, Not p)))
                                  leftHandTerms
        transformedRightHandSide = transform rightHandTerms
        clauses = transformedLeftHandSide <> transformedRightHandSide
        k =   fromIntegral (sum (fmap fst transformedLeftHandSide))
            + denominatorProduct * (leftHandConstant - rightHandConstant)
            + if strict then 0 else 1

-- TODO: Use Data.Map
extractPropositions :: Probability p -> [(Rational, Propositional p)]
extractPropositions (Pr p)    = [(1,p)]
extractPropositions (Const _) = []
extractPropositions (x :+ y)  = extractPropositions x ++ extractPropositions y
extractPropositions (a :* x)  =
  fmap (\(c,p) -> (a * c, p)) (extractPropositions x)

extractConstantTerm :: Probability p -> Rational
extractConstantTerm (Pr _)    = 0
extractConstantTerm (Const d) = d
extractConstantTerm (x :+ y)  = extractConstantTerm x + extractConstantTerm y
extractConstantTerm (a :* x)  = a * extractConstantTerm x

summationNormalForm :: ProbabilityInequality p
                    -> GTSummationNormalForm (Propositional p)
summationNormalForm (b :>  a) = summationNormalForm (a :<  b)
summationNormalForm (b :>= a) = summationNormalForm (a :<= b)
summationNormalForm (a :< b)  = (summationNormalForm (a :<= b)) {strict = True}
summationNormalForm (a :<= b) =
  GTSummationNormalForm { leftHandTerms = extractPropositions a
                        , leftHandConstant = extractConstantTerm a
                        , rightHandTerms = extractPropositions b
                        , rightHandConstant = extractConstantTerm b
                        , strict = False }

-- | Determine if the largest sublist of CNFs simultaneously satisfiable
--   has weight no bigger than `k`
maxSatN :: (Ord a, MonadPlus m, ModelSearch m model (CNF a))
        => Integer
        -> [(Integer, CNF a)]
        -> m model
maxSatN k = msum . fmap (findModel . Data.Foldable.fold) . chooseN
 where
   totalWeight = sum . fmap fst
   chooseN :: [(Integer, CNF a)] -> [[CNF a]]
   chooseN xs = weightedChoose xs (totalWeight xs) (k + 1)

instance ( Ord p
         , MonadPlus m
         , ModelSearch m model (ConjClause p) )
         => ModelSearch m model (ProbabilityInequality p)
  where
    findModel = findModel . summationNormalForm
