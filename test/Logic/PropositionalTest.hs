{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# OPTIONS_GHC -fno-warn-orphans  #-}
module Logic.PropositionalTest (propositionalTests)
where

import           Control.Applicative   (Alternative, empty, pure)
import           Control.Monad         (liftM2)
import qualified Data.Maybe            (isJust, isNothing)
import           Data.Monoid           ((<>))
import qualified Data.Set              (Set, filter, map, member)
import           Logic.CNF             (ConjClause, Literal (Neg, Pos))
import           Logic.Propositional   ( Propositional (..)
                                       , Probability (..)
                                       , probGT )
import           Logic.Semantics       ( ModelSearch (findModel)
                                       , Semantics ((|=)))
import           Test.QuickCheck       ( Arbitrary (arbitrary)
                                       , Gen, oneof, sized )
import           Test.Tasty            (TestTree, testGroup)
import           Test.Tasty.HUnit      (assert, testCase, (@?=))
import           Test.Tasty.QuickCheck (testProperty)

instance Arbitrary p => Arbitrary (Propositional p) where
  arbitrary = sized sizedArbitraryProposition
    where
      -- | Create a propositional formula that has at most depth n
      sizedArbitraryProposition :: Arbitrary p => Int -> Gen (Propositional p)
      sizedArbitraryProposition n
        | n <= 0 = fmap Proposition arbitrary
        | otherwise =
          oneof [ fmap Proposition arbitrary
                , liftM2 (:&&:) halfSizeSubFormula halfSizeSubFormula
                , liftM2 (:||:) halfSizeSubFormula halfSizeSubFormula
                , liftM2 (:->:) halfSizeSubFormula halfSizeSubFormula
                , fmap Not (sizedArbitraryProposition (n - 1))
                , return Verum
                , return Falsum ]
        where
          halfSizeSubFormula = sizedArbitraryProposition (n `div` 2)

instance Ord p => Semantics (Data.Set.Set p) (ConjClause p) where
  (|=) m = all checkSatisfied
    where
      checkSatisfied (Pos p) = p `Data.Set.member` m
      checkSatisfied (Neg p) = not (p `Data.Set.member` m)

-- | ModelSearch for free boolean logic, with no underlying decision procedure
instance (Ord p, Alternative f) => ModelSearch f (Data.Set.Set p) (ConjClause p)
  where
    findModel clause =
      if any ((`Data.Set.member` clause) . neg) clause
      then empty
      else (pure . Data.Set.map project . Data.Set.filter positive) clause
      where
        neg (Pos a) = Neg a
        neg (Neg a) = Pos a
        project (Pos a) = a
        project (Neg a) = a
        positive (Pos _) = True
        positive (Neg _) = False

propositionalIdentitiesHUnit :: TestTree
propositionalIdentitiesHUnit = testGroup "Simple Model Search Tests" $
  let
    a = Proposition 'a'
    b = Proposition 'b'
    c = Proposition 'c'
    findModel' = findModel :: Propositional Char -> Maybe (Data.Set.Set Char)
  in
    [
      testCase "No m s.t. `m |= (Verum :->: Falsum)`"
      $ findModel' (Verum :->: Falsum) @?= Nothing
    , testCase "No m s.t. `m |= Falsum`"
      $ findModel' Falsum @?= Nothing
    , testCase "Exists m s.t. `m |= Verum` "
      $ (assert . Data.Maybe.isJust . findModel') Verum
    , testCase "Exists m s.t. `m |= a`"
      $ (assert . Data.Maybe.isJust . findModel') a
    , testCase "Exists m s.t. `(m |= Not a) && not (m |= a)`"
      $ fmap (|= a) (findModel' (Not a)) @?= Just False
    , testCase "Exists m s.t. `(m |= (a :||: b)) && ((m |= a) || (m |= b))`"
      $ let searchResult = findModel' (a :||: b) in
         assert ( (fmap (|= a) searchResult == Just True)
                 || (fmap (|= b) searchResult == Just True) )
    , testCase ( "Exists m s.t. `(m |= Not (a :||: b)) "
                <> "&& not (m |= a) && not (m |= b)`" )
      $ let searchResult = findModel' (Not (a :||: b)) in
         assert ( (fmap (|= a) searchResult == Just False)
                 && (fmap (|= b) searchResult == Just False) )
     , testCase ( "Exists m s.t. `m |= Not (p && q) "
                 <> "&& (not (m |= a) || not (m |= b))`" )
       $ let searchResult = findModel' (Not (a :&&: b)) in
         assert ( (fmap (|= a) searchResult == Just False)
                 || (fmap (|= b) searchResult == Just False) )
     , testCase ( "Exists m s.t. `(m |= (a :&&: (b :||: c))) "
                  <> "&& (m |= (a :&&: b) || m |= (a :&&: c))`" )
       $ let searchResult = findModel' (a :&&: (b :||: c)) in
         assert ( (fmap (|= (a :&&: b)) searchResult == Just True)
                 || (fmap (|= (a :&&: c)) searchResult == Just True) )
    ]

propositionalSemanticsQC :: TestTree
propositionalSemanticsQC = testGroup "Propositional Semantics Laws" $
  let
    findModel' = findModel :: Propositional Char -> Maybe (Data.Set.Set Char)
  in
    [
      testProperty
      ( "Forall f: "
      <> "`fmap (|= f) (findModel f) == fmap (const True) (findModel f)`" )
      $ \ f -> fmap (|= f) (findModel' f) == fmap (const True) (findModel' f)
    ]

probabilityTheoryQC :: TestTree
probabilityTheoryQC = testGroup "Probability Theory Identities" $
  let
    a = Proposition 'a'
    b = Proposition 'b'
    probGT' = probGT :: Probability Char
                     -> Probability Char
                     -> Maybe (Data.Set.Set Char)
  in
    [
      testProperty "Forall x, y, and Pr: Pr (x :&&: y) <= Pr (x :&&: y)"
      $ \ (x :: Propositional Char) y ->
        Data.Maybe.isNothing
        $ Pr (x :&&: y) `probGT'` Pr (x :&&: y)
    , testProperty
      "Forall x, y, and Pr: Pr x :+ Pr y <= Pr (x :||: y) :+ Pr (x :&&: y)"
      $ \ (x :: Propositional Char) y ->
        Data.Maybe.isNothing
        $ (Pr x :+ Pr y) `probGT'` (Pr (x :||: y) :+ Pr (x :&&: y))
    , testProperty
      "Forall x, y, and Pr: Pr x :+ Pr y <= Pr (x :||: y) :+ Pr (x :&&: y)"
      $ \ (x :: Propositional Char) y ->
        Data.Maybe.isNothing
        $ (Pr x :+ Pr y) `probGT'` (Pr (x :||: y) :+ Pr (x :&&: y))
    , testCase "Exists Pr s.t. Pr a :+ Pr b > Pr (a :||: b)"
      $ assert . Data.Maybe.isJust
        $ (Pr a :+ Pr b) `probGT'` Pr (a :||: b)
    , testProperty "Forall x, and Pr: 1 <= Pr x :+ Pr (Not x)"
      $ \ (x :: Propositional Char) ->
        Data.Maybe.isNothing $ Const 1 `probGT'` (Pr x :+ Pr (Not x))
    , testProperty "Forall x, and Pr: Pr x :+ Pr (Not x) <= 1"
      $ \ (x :: Propositional Char) ->
        Data.Maybe.isNothing $ (Pr x :+ Pr (Not x)) `probGT'` Const 1 
    ]

propositionalTests :: TestTree
propositionalTests =
  testGroup "Propositional Tests" [ propositionalIdentitiesHUnit
                                  , propositionalSemanticsQC
                                  , probabilityTheoryQC ]

-- extractPropositionalAtoms :: Ord a => Propositional a -> Set.Set a
-- extractPropositionalAtoms Verum           = Set.empty
-- extractPropositionalAtoms Falsum          = Set.empty
-- extractPropositionalAtoms (Proposition p) = Set.fromList [p]
-- extractPropositionalAtoms (Not x)         = extractPropositionalAtoms x
-- extractPropositionalAtoms (x :&: y)       = unionPropositionalAtoms x y
-- extractPropositionalAtoms (x :|: y)       = unionPropositionalAtoms x y
-- extractPropositionalAtoms (x :->: y)      = unionPropositionalAtoms x y
--
-- unionPropositionalAtoms
--   :: Ord a
--   => Propositional a
--   -> Propositional a
--   -> Set.Set a
-- unionPropositionalAtoms x y =
--   extractPropositionalAtoms x `mappend` extractPropositionalAtoms y
--
-- extractClauseAtoms
--   :: Ord a
--   => Set.Set (Set.Set (Literal (Definitional a)))
--   -> Set.Set a
-- extractClauseAtoms = extractAtoms . Set.toList . unions
--   where
--     unions                     = Set.foldr Set.union Set.empty
--     extractVariable (Pos x) = x
--     extractVariable (Neg x) = x
--     addAtom (Definition _) set = set
--     addAtom (Atom a) set       = Set.insert a set
--     extractAtoms               = foldr (addAtom . extractVariable) Set.empty
--
-- -- | Double turnstyle (models) evaluator
-- (|=) :: Ord a => Set.Set a -> Propositional a -> Bool
-- m |= (Proposition p) = p `Set.member` m
-- m |= (Not f)         = not (m |= f)
-- m |= (a :&: b)       = (m |= a) && (m |= b)
-- m |= (a :|: b)       = (m |= a) || (m |= b)
-- m |= (a :->: b)      = m |= (Not a :|: b)
-- _ |= Verum           = True
-- _ |= Falsum          = False
--
-- extractModelFromDPLLSat :: Ord a => Set.Set (Definitional a) -> Set.Set a
-- extractModelFromDPLLSat = Set.fold addAtom Set.empty
--   where
--     addAtom (Atom a) collectedAtoms       = Set.insert a collectedAtoms
--     addAtom (Definition _) collectedAtoms = collectedAtoms
--
-- test_generativeTseitin :: TestTree
-- test_generativeTseitin = testGroup "Tseitin Generative Tests"
--   [
--     testProperty "Tseitin transformation preserves propositional atoms"
--       $ \(p :: Propositional Char) -> extractPropositionalAtoms p
--               == (extractClauseAtoms . head . definitionalClauses) [p]
--   , testProperty "Models found for clauses for Tseitin transformed proposition satisfy original proposition"
--       $ \(p :: Propositional Char) -> case dpllProposition p of
--                 Nothing -> True
--                 Just m  -> m |= p
--   ]
--
--
-- interleave :: [a] -> [a] -> [a]
-- interleave [] ys     = ys
-- interleave (x:xs) ys = x : interleave ys xs
--
-- subLists :: [a] -> [[a]]
-- subLists [] = [[]]
-- subLists (x:xs) = let powerXs = subLists xs in powerXs `interleave` map (x:) powerXs
--
-- findLargerSubLists :: Int -> [a] -> [[a]]
-- findLargerSubLists n xs = filter (\x -> length x > n) (subLists xs)
--
-- maxSatN
--   :: (Ord p, MonadPlus m)
--   => Int
--   -> [Set.Set (Clause p)]
--   -> m (Set.Set p)
-- maxSatN n clausesList =
--   if n <= 0
--   then mzero
--   else msum ( map (dpll . Set.unions) (findLargerSubLists n clausesList) )
--
-- data ProbabilityInequality a = ProbabilityExpression a :<= ProbabilityExpression a
-- data ProbabilityExpression a = Constant Double
--                              | Probability (Propositional a)
--                              | ProbabilityExpression a :+ ProbabilityExpression a
--
-- extractConstantTerm :: ProbabilityExpression a -> Double
-- extractConstantTerm (Constant x) = x
-- extractConstantTerm (Probability _) = 0
-- extractConstantTerm (a :+ b) = extractConstantTerm a + extractConstantTerm b
--
-- extractPropositions :: ProbabilityExpression a -> [Propositional a]
-- extractPropositions (Constant _) = mempty
-- extractPropositions (Probability x) = return x
-- extractPropositions (a :+ b) = extractPropositions a `mappend` extractPropositions b
--
-- disproveProbabilityInequality
--   :: (Ord a, MonadPlus m)
--   => ProbabilityInequality a
--   -> m (Set.Set a)
-- disproveProbabilityInequality (leftHandSide :<= rightHandSide) =
--   fmap extractModelFromDPLLSat ( maxSatN adjustedRightHandLength clauses )
--   where
--     leftHandPropositions    = extractPropositions leftHandSide
--     rightHandPropositions   = extractPropositions rightHandSide
--     rightHandLength         = length rightHandPropositions
--     adjustedRightHandLength = floor (  fromIntegral rightHandLength
--                                      + extractConstantTerm rightHandSide
--                                      - extractConstantTerm leftHandSide)
--     clauses = definitionalClauses (fmap Not rightHandPropositions `mappend` leftHandPropositions)
--
-- test_probabilityTheory :: TestTree
-- test_probabilityTheory = testGroup "Probability Theory Identities"
--    [
--      testProperty "⊢ ∀ϕ. ∀ψ. Pr ϕ + Pr ψ ≤ Pr (ϕ∨ψ) + Pr (ϕ∧ψ)"
--      $ \(p :: Propositional Char) q ->
--        Data.Maybe.isNothing
--        $ disproveProbabilityInequality
--          ((Probability p :+ Probability q ) :<= (Probability (p :|: q) :+ Probability (p :&: q)))
--    , testProperty "⊢ ∀ϕ. ∀ψ. Pr (ϕ ∨ ψ) + Pr (ϕ ∧ ψ) ≤ Pr ϕ + Pr ψ"
--      $ \(p :: Propositional Char) q ->
--        Data.Maybe.isNothing
--        $ disproveProbabilityInequality
--          ((Probability (p :|: q) :+ Probability (p :&: q)) :<= (Probability p :+ Probability q))
--    , testProperty "⊢ ∀ϕ. 0.5 ≤ Pr ϕ + Pr (¬ ϕ)"
--      $ \(p :: Propositional Char) ->
--        Data.Maybe.isNothing
--        $ disproveProbabilityInequality
--          (Constant 0.05 :<= (Probability p :+ Probability (Not p)))
--    , testProperty "⊢ ∀ϕ. ∀ψ. ∀ξ. 2 ⨉ Pr ϕ ≤ Pr (¬ (ψ ∧ (ξ -> ¬ ϕ))) + Pr (¬ (ξ ∧ (ψ -> ¬ ϕ))) + Pr (¬ ((ψ -> ¬ ϕ) ∧ (ξ -> ¬ ϕ)))"
--      $ \(p :: Propositional Char) q r ->
--        Data.Maybe.isNothing
--        $ disproveProbabilityInequality
--          ((Probability p :+ Probability p)
--           :<= (   Probability (Not (q :&: (r :->: Not p)))
--                :+ Probability (Not (r :&: (q :->: Not p)))
--                :+ Probability (Not ((r :->: Not p) :&: (q :->: Not p)))))
--    ]

