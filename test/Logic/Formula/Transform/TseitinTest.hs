{-# LANGUAGE ScopedTypeVariables #-}
module Logic.Formula.Transform.TseitinTest
  (test_generativeTseitin,
   test_hunitTseitin,
   test_probabilityTheory) where

import           Control.Monad                               (MonadPlus, msum,
                                                              mzero)
import qualified Data.Maybe
import qualified Data.Set                                    as Set
import           Logic.Formula.Data.Literal
import           Logic.Formula.Data.Propositional
import           Logic.Formula.Data.Propositional.QuickCheck ()
import           Logic.Formula.Transform.Tseitin
import           Logic.Satisfaction.PropositionalSat
import           Logic.Satisfaction.Sat
import           Test.Tasty
import           Test.Tasty.HUnit
import           Test.Tasty.QuickCheck

extractPropositionalAtoms :: Ord a => Propositional a -> Set.Set a
extractPropositionalAtoms Verum           = Set.empty
extractPropositionalAtoms Falsum          = Set.empty
extractPropositionalAtoms (Proposition p) = Set.fromList [p]
extractPropositionalAtoms (Not x)         = extractPropositionalAtoms x
extractPropositionalAtoms (x :&: y)       = unionPropositionalAtoms x y
extractPropositionalAtoms (x :|: y)       = unionPropositionalAtoms x y
extractPropositionalAtoms (x :->: y)      = unionPropositionalAtoms x y

unionPropositionalAtoms
  :: Ord a
  => Propositional a
  -> Propositional a
  -> Set.Set a
unionPropositionalAtoms x y =
  extractPropositionalAtoms x `mappend` extractPropositionalAtoms y

extractClauseAtoms
  :: Ord a
  => Set.Set (Set.Set (Literal (Definitional a)))
  -> Set.Set a
extractClauseAtoms = extractAtoms . Set.toList . unions
  where
    unions                     = Set.foldr Set.union Set.empty
    extractVariable (Pos x) = x
    extractVariable (Neg x) = x
    addAtom (Definition _) set = set
    addAtom (Atom a) set       = Set.insert a set
    extractAtoms               = foldr (addAtom . extractVariable) Set.empty

-- | Double turnstyle (models) evaluator
(|=) :: Ord a => Set.Set a -> Propositional a -> Bool
m |= (Proposition p) = p `Set.member` m
m |= (Not f)         = not (m |= f)
m |= (a :&: b)       = (m |= a) && (m |= b)
m |= (a :|: b)       = (m |= a) || (m |= b)
m |= (a :->: b)      = m |= (Not a :|: b)
_ |= Verum           = True
_ |= Falsum          = False

extractModelFromDPLLSat :: Ord a => Set.Set (Definitional a) -> Set.Set a
extractModelFromDPLLSat = Set.fold addAtom Set.empty
  where
    addAtom (Atom a) collectedAtoms       = Set.insert a collectedAtoms
    addAtom (Definition _) collectedAtoms = collectedAtoms

test_generativeTseitin :: TestTree
test_generativeTseitin = testGroup "Tseitin Generative Tests"
  [
    testProperty "Tseitin transformation preserves propositional atoms"
      $ \(p :: Propositional Char) -> extractPropositionalAtoms p
              == (extractClauseAtoms . head . definitionalClauses) [p]
  , testProperty "Models found for clauses for Tseitin transformed proposition satisfy original proposition"
      $ \(p :: Propositional Char) -> case dpllProposition p of
                Nothing -> True
                Just m  -> m |= p
  ]

test_hunitTseitin :: TestTree
test_hunitTseitin = testGroup "Tseitin Unit Tests"
  [
    testCase "∄ℳ. ℳ ⊨ ⊤ → ⊥" $ dpllProposition (Verum :->: Falsum :: Propositional Char) @?= Nothing
  , testCase "∄ℳ. ℳ ⊨ ⊥" $ dpllProposition (Falsum :: Propositional Char) @?= Nothing
  , testCase "∃ℳ. ℳ ⊨ ⊤" $ assert (Data.Maybe.isJust (dpllProposition (Verum :: Propositional Char)))
  ]

interleave :: [a] -> [a] -> [a]
interleave [] ys     = ys
interleave (x:xs) ys = x : interleave ys xs

subLists :: [a] -> [[a]]
subLists [] = [[]]
subLists (x:xs) = let powerXs = subLists xs in powerXs `interleave` map (x:) powerXs

findLargerSubLists :: Int -> [a] -> [[a]]
findLargerSubLists n xs = filter (\x -> length x > n) (subLists xs)

maxSatN
  :: (Ord p, MonadPlus m)
  => Int
  -> [Set.Set (Clause p)]
  -> m (Set.Set p)
maxSatN n clausesList =
  if n <= 0
  then mzero
  else msum ( map (dpll . Set.unions) (findLargerSubLists n clausesList) )

data ProbabilityInequality a = ProbabilityExpression a :<= ProbabilityExpression a
data ProbabilityExpression a = Constant Double
                             | Probability (Propositional a)
                             | ProbabilityExpression a :+ ProbabilityExpression a

extractConstantTerm :: ProbabilityExpression a -> Double
extractConstantTerm (Constant x) = x
extractConstantTerm (Probability _) = 0
extractConstantTerm (a :+ b) = extractConstantTerm a + extractConstantTerm b

extractPropositions :: ProbabilityExpression a -> [Propositional a]
extractPropositions (Constant _) = mempty
extractPropositions (Probability x) = return x
extractPropositions (a :+ b) = extractPropositions a `mappend` extractPropositions b

disproveProbabilityInequality
  :: (Ord a, MonadPlus m)
  => ProbabilityInequality a
  -> m (Set.Set a)
disproveProbabilityInequality (leftHandSide :<= rightHandSide) =
  fmap extractModelFromDPLLSat ( maxSatN adjustedRightHandLength clauses )
  where
    leftHandPropositions    = extractPropositions leftHandSide
    rightHandPropositions   = extractPropositions rightHandSide
    rightHandLength         = length rightHandPropositions
    adjustedRightHandLength = floor (  fromIntegral rightHandLength
                                     + extractConstantTerm rightHandSide
                                     - extractConstantTerm leftHandSide)
    clauses = definitionalClauses (fmap Not rightHandPropositions `mappend` leftHandPropositions)

test_probabilityTheory :: TestTree
test_probabilityTheory = testGroup "Probability Theory Identities"
   [
     testProperty "⊢ ∀ϕ. ∀ψ. Pr ϕ + Pr ψ ≤ Pr (ϕ∨ψ) + Pr (ϕ∧ψ)"
     $ \(p :: Propositional Char) q ->
       Data.Maybe.isNothing
       $ disproveProbabilityInequality
         ((Probability p :+ Probability q ) :<= (Probability (p :|: q) :+ Probability (p :&: q)))
   , testProperty "⊢ ∀ϕ. ∀ψ. Pr (ϕ ∨ ψ) + Pr (ϕ ∧ ψ) ≤ Pr ϕ + Pr ψ"
     $ \(p :: Propositional Char) q ->
       Data.Maybe.isNothing
       $ disproveProbabilityInequality
         ((Probability (p :|: q) :+ Probability (p :&: q)) :<= (Probability p :+ Probability q))
   , testProperty "⊢ ∀ϕ. 0.5 ≤ Pr ϕ + Pr (¬ ϕ)"
     $ \(p :: Propositional Char) ->
       Data.Maybe.isNothing
       $ disproveProbabilityInequality
         (Constant 0.05 :<= (Probability p :+ Probability (Not p)))
   , testProperty "⊢ ∀ϕ. ∀ψ. ∀ξ. 2 ⨉ Pr ϕ ≤ Pr (¬ (ψ ∧ (ξ → ¬ ϕ))) + Pr (¬ (ξ ∧ (ψ → ¬ ϕ))) + Pr (∼((ψ → ¬ ϕ) ∧ (ξ → ¬ ϕ)))"
     $ \(p :: Propositional Char) q r ->
       Data.Maybe.isNothing
       $ disproveProbabilityInequality
         ((Probability p :+ Probability p)
          :<= (   Probability (Not (q :&: (r :->: Not p)))
               :+ Probability (Not (r :&: (q :->: Not p)))
               :+ Probability (Not ((r :->: Not p) :&: (q :->: Not p)))))
   ]
