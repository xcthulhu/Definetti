{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# OPTIONS_GHC -fno-warn-orphans  #-}

module Logic.Tasty.Suite.TemporalTest (temporalTests, temporalSemanticsQC)
where

import           Data.List.NonEmpty    (NonEmpty)
import           Data.Monoid           ((<>))
import           Test.QuickCheck       (Arbitrary (arbitrary), oneof, within)
import           Test.Tasty            (TestTree, testGroup)
import           Test.Tasty.HUnit      (testCase, (@?=))
import           Test.Tasty.QuickCheck (testProperty)

import           Logic.Propositional   (FreeModel, Propositional ((:&&:), Falsum, Not, Proposition, Verum))
import           Logic.Semantics       (ModelSearch (findModel),
                                        Semantics ((|=)))
import           Logic.Temporal        (Temporal (Always, Until),
                                        TemporalFormula (TemporalFormula),
                                        before)

import           Logic.TestAtom        (Atom, AtomModel, bound)


instance Arbitrary p => Arbitrary (Temporal p) where
  arbitrary = oneof [ Until <$> arbitrary <*> arbitrary, Always <$> arbitrary]

instance (Arbitrary p, Arbitrary v) => Arbitrary (TemporalFormula v p) where
  arbitrary = TemporalFormula <$> arbitrary

temporalLogicTests :: TestTree
temporalLogicTests = testGroup
  "Temporal Logic Tests"
  [
    testCase "`a before b` AND `b before c` implies `a before c`" $
    ((|= (a `before` c)) <$>
     findModel' ((a `before` b) :&&: (b `before` c))) @?= Just True
  , testCase "Should not find a model for `Not (Always Verum)`" $
    findModel' (Not (Proposition (Always Verum))) @?= Nothing
  , testCase "Should not find a model for `Always Falsum`" $
    findModel' (Proposition (Always Falsum)) @?= Nothing
  , testCase "Should not find a model for `Not ((Always Verum) :&&: Verum)`" $
    findModel' (Not (Proposition (Always Verum) :&&: Verum)) @?= Nothing
  ]
 where
  [a,b,c] = Proposition . bound <$> ['a', 'b', 'c']
  findModel' :: Propositional (Temporal (Propositional (Atom Char)))
           -> Maybe (NonEmpty (AtomModel Char))
  findModel' = findModel

temporalSemanticsQC :: TestTree
temporalSemanticsQC =
  testGroup "Temporal Semantics Laws"
  [ testProperty
        (  "Forall f: `fmap (|= f) (findModel f)"
        <> " == fmap (const True) (findModel f)`"
        )
      $ within 100000000
      $ \f -> let m = findModel'' f
              in fmap (|= f) m == fmap (const True) m
  ] where
    findModel'' :: TemporalFormula Char (Propositional (Atom Char))
                -> Maybe (FreeModel Char (NonEmpty (AtomModel Char)))
    findModel'' = findModel

temporalTests :: TestTree
temporalTests = testGroup
  "Temporal Tests"
  [ temporalLogicTests
  , temporalSemanticsQC
  ]
