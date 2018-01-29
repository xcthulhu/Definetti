{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE UndecidableInstances  #-}
module Logic.Probability ( Probability (..)
                         , ProbabilityInequality (..))
where
import           Logic.Propositional (Propositional (Not))
import           Logic.Propositional.Tseitin (tseitinTransform)
import           Control.Monad   (MonadPlus)
import           Logic.Propositional.DPLL (ConjClause, Clause, maxSatN)
import           Logic.Semantics (ModelSearch (findModel), Semantics ((|=)))

-- | Probability Inequalities

data Probability p = Pr (Propositional p)
                   | Const Double
                   | (Probability p) :+ (Probability p)

data ProbabilityInequality p = (Probability p) :< (Probability p)
                             | (Probability p) :> (Probability p)

instance Semantics model (Clause p) =>
         Semantics model (ProbabilityInequality p) where
  m |= (a :< b) = m |= (b :> a)
  m |= (a :> b) = evalProbability a > evalProbability b
    where
      evalProbability (Const c) = c
      evalProbability (Pr p) = if m |= p then 1 else 0
      evalProbability (x :+ y) = evalProbability x + evalProbability y

extractPropositions :: Probability p -> [Propositional p]
extractPropositions (Pr    p) = [p]
extractPropositions (Const _) = []
extractPropositions (x :+ y ) = extractPropositions x ++ extractPropositions y

extractConstantTerm :: Probability p -> Double
extractConstantTerm (Pr    _) = 0
extractConstantTerm (Const d) = d
extractConstantTerm (x :+ y ) = extractConstantTerm x + extractConstantTerm y

instance ( Ord p
         , MonadPlus m
         , ModelSearch m model (ConjClause p) )
         => ModelSearch m model (ProbabilityInequality p)
  where
    findModel (a :< b) = findModel (b :> a)
    findModel (b :> a) = maxSatN capacity clauses
     where
        leftHandPropositions = extractPropositions b
        rightHandPropositions = extractPropositions a
        clauses = fmap tseitinTransform
                       (fmap Not rightHandPropositions ++ leftHandPropositions)
        capacity = floor
          ( fromIntegral (length rightHandPropositions)
          + extractConstantTerm a
          - extractConstantTerm b)
