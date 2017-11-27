{-# LANGUAGE ScopedTypeVariables #-}
module Logic.Formula.Transform.TseitinTest (test_tseitin) where

import qualified Data.Set                                    as Set
import           Logic.Formula.Data.Literal
import           Logic.Formula.Data.Propositional
import           Logic.Formula.Data.Propositional.QuickCheck ()
import           Logic.Formula.Transform.Tseitin
import           Logic.Satisfaction.Sat
import           Test.Tasty
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
    unions = Set.foldl Set.union Set.empty
    extractVariable (Pos x) = x
    extractVariable (Neg x) = x
    addAtom set (Definition _) = set
    addAtom set (Atom a)       = Set.insert a set
    extractAtoms literals =
      foldl addAtom Set.empty (map extractVariable literals)

-- | Double turnstyle (models) evaluator
(|=) :: Ord a => Set.Set a -> Propositional a -> Bool
m |= (Proposition p) = p `Set.member` m
m |= (Not f)         = not (m |= f)
m |= (a :&: b)       = (m |= a) && (m |= b)
m |= (a :|: b)       = (m |= a) || (m |= b)
m |= (a :->: b)      = m |= ((Not a) :|: b)
_ |= Verum           = True
_ |= Falsum          = False

extractModelFromDPLLSat :: Ord a => Set.Set (Definitional a) -> Set.Set a
extractModelFromDPLLSat = Set.fold addAtom Set.empty
  where
    addAtom (Atom a) collectedAtoms       = Set.insert a collectedAtoms
    addAtom (Definition _) collectedAtoms = collectedAtoms

dpllMaybeModel :: Ord a => Propositional a -> Maybe (Set.Set a)
dpllMaybeModel = fmap extractModelFromDPLLSat . dpll . Set.unions . definitionalClauses . (:[])

test_tseitin :: TestTree
test_tseitin = testGroup "Tseitin Tests"
  [
    testProperty "Tseitin transformation preserves propositional atoms"
     $ \p -> extractPropositionalAtoms (p :: Propositional Int)
             == (extractClauseAtoms . head . definitionalClauses) [p]
  , testProperty "Models found for clauses for Tseitin transformed proposition satisfy original proposition"
     $ \p -> case (dpllMaybeModel (p :: Propositional Int)) of
               Nothing -> True
               Just m  -> m |= p
  ]
