{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# OPTIONS_GHC -fno-warn-orphans  #-}

module Logic.Tasty.Suite.TemporalTest (temporalTests, temporalSemanticsQC)
where

import           Data.List.NonEmpty    (NonEmpty)
import           Test.QuickCheck       (Arbitrary (arbitrary), oneof)
import           Test.Tasty            (TestTree, testGroup)
import           Test.Tasty.HUnit      (testCase, (@?=))
import           Test.Tasty.QuickCheck (testProperty)

import           Logic.Propositional   (FreeModel, FreeVars (Bound), Propositional ((:&&:), Falsum, Not, Proposition, Verum))
import           Logic.Semantics       (ModelSearch (findModel),
                                        Semantics ((|=)))
import           Logic.Temporal        (Temporal (Always, Until), before)

import           Logic.TestAtom        (Atom, AtomModel, bound)


instance Arbitrary p => Arbitrary (Temporal (Propositional p)) where
  arbitrary = oneof [ Until <$> arbitrary <*> arbitrary, Always <$> arbitrary ]

findModel' :: Propositional (FreeVars Char (Temporal (Propositional (Atom Char))))
           -> Maybe (FreeModel Char (NonEmpty (AtomModel Char)))
findModel' = findModel

before' :: Propositional (Atom Char)
        -> Propositional (Atom Char)
        -> Propositional (FreeVars Char (Temporal (Propositional (Atom Char))))
a `before'` b = Bound <$> (a `before` b)

always' :: Propositional (Atom Char)
        -> Propositional (FreeVars Char (Temporal (Propositional (Atom Char))))
always' = Proposition . Bound . Always

slowTemporalLogicTests :: TestTree
slowTemporalLogicTests = testGroup
  "Temporal Logic Tests"
  [
    testCase "`a before b` AND `b before c` implies `a before c`" $
    ((|= (a `before'` c)) <$>
     findModel' ((a `before'` b) :&&: (b `before'` c))) @?= Just True
  , testCase "Should not find a model for `Not (Always Verum)`" $
    findModel' (Not (always' Verum)) @?= Nothing
  , testCase "Should not find a model for `Always Falsum`" $
    findModel' (always' Falsum) @?= Nothing
  , testCase "Should not find a model for `Not ((Always Verum) :&&: Verum)`" $
    findModel' (Not (always' Verum) :&&: Verum) @?= Nothing
  ]
 where
  [a,b,c] = Proposition . bound <$> ['a', 'b', 'c']

temporalSemanticsQC :: TestTree
temporalSemanticsQC =
  testGroup "Temporal Semantics Laws"
  [ testProperty "Forall f: `fmap (|= f) (findModel f) == fmap (const True) (findModel f)`"
      $ \f -> let m = findModel' f
              in fmap (|= f) m == fmap (const True) m
  ]

temporalTests :: TestTree
temporalTests = testGroup
  "Temporal Logic Tests"
    [ slowTemporalLogicTests
    , temporalSemanticsQC
    ]
