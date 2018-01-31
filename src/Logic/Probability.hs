{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE UndecidableInstances  #-}
module Logic.Probability ( Probability (..)
                         , ProbabilityInequality (..))
where
import           Control.Applicative         (Alternative, empty, pure, (<|>))
import           Control.Monad               (MonadPlus, msum)
import           Data.DList                  (DList)
import qualified Data.Foldable               (fold)
import           Logic.Propositional         (Propositional (Not))
import           Logic.Propositional.DPLL    (CNF, Clause, ConjClause)
import           Logic.Propositional.Tseitin (tseitinTransform)
import           Logic.Semantics             (ModelSearch (findModel),
                                              Semantics ((|=)))

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
      evalProbability (Pr p)    = if m |= p then 1 else 0
      evalProbability (x :+ y)  = evalProbability x + evalProbability y

extractPropositions :: Probability p -> [Propositional p]
extractPropositions (Pr    p) = [p]
extractPropositions (Const _) = []
extractPropositions (x:+y   ) = extractPropositions x ++ extractPropositions y

extractConstantTerm :: Probability p -> Double
extractConstantTerm (Pr    _) = 0
extractConstantTerm (Const d) = d
extractConstantTerm (x:+y   ) = extractConstantTerm x + extractConstantTerm y

-- TODO: Use ListLike
-- TODO: Use interleave https://mail.haskell.org/pipermail/haskell-cafe/2003-June/004484.html

-- | Choose `k` elements of a collection of `n` items
--   Results in `n choose k = n! / (k!(n-k)!)`
--   Lifted into an `Alternative` functor (so DList may be used)
choose :: Alternative f => [a] -> Int -> Int -> f [a]
choose clauses n k
  | k < 0             = empty
  | k > n             = empty
  | k == 0            = pure []
  | [] <- clauses     = empty
  | k == n            = pure clauses
  | (x:xs) <- clauses = choose xs n' k <|> fmap (x :) (choose xs n' (k - 1))
  where n' = n - 1

-- powerList :: Alternative f => [a] -> f [a]
-- powerList xs = Data.Foldable.asum
--   (fmap (choose xs total) [total, total - 1 .. 0])
--   where total = length xs

-- -- | Find the largest sublist of CNFs simultaneously satisfiable from a list
-- maxSat
--   :: (Ord a, MonadPlus m, ModelSearch m model (CNF a))
--   => [CNF a]
--   -> m ([CNF a], model)
-- maxSat =
--   msum
--     . fmap (\cs -> (,) cs <$> (findModel . Data.Foldable.fold) cs)
--     . (powerList :: [a] -> DList [a])

-- | Determine if the largest sublist of CNFs simultaneously satisfiable
--   has length no bigger than `n`
maxSatN
  :: (Ord a, MonadPlus m, ModelSearch m model (CNF a))
  => Int
  -> [CNF a]
  -> m model
maxSatN n = msum . fmap (findModel . Data.Foldable.fold) . chooseN
 where
  chooseN :: [a] -> DList [a]
  chooseN xs = choose xs (length xs) (n + 1)

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
