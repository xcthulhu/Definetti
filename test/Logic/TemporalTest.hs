{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# OPTIONS_GHC -fno-warn-orphans  #-}

module Logic.TemporalTest (temporalTests)
where

import           Test.QuickCheck         (Arbitrary (arbitrary), oneof)
import           Test.Tasty              (TestTree, testGroup)
import           Test.Tasty.HUnit        (testCase, (@?=))

import           Logic.Propositional     (Propositional ((:&&:), Proposition))
import           Logic.Semantics         (ModelSearch (findModel),
                                          Semantics ((|=)))
import           Logic.Temporal          (Temporal (Always, Until), before)

import           Logic.PropositionalTest (Atom, AtomModel, bound)


instance Arbitrary p => Arbitrary (Temporal (Propositional p)) where
  arbitrary = oneof [ Until <$> arbitrary <*> arbitrary, Always <$> arbitrary]

temporalLogicTests :: TestTree
temporalLogicTests = testGroup
  "Temporal Logic Tests"
  [
    testCase "'a before b' AND 'b before c' implies 'a before c'" $
    (
      (|= (a `before` c)) <$>
      findModel' ((a `before` b) :&&: (b `before` c))) @?= Just True
  ]
 where
  [a,b,c] = Proposition . bound <$> ['a', 'b', 'c']
  findModel' :: Propositional (Temporal (Propositional (Atom Char)))
             -> Maybe [AtomModel Char]
  findModel' = findModel

temporalTests :: TestTree
temporalTests = testGroup
  "Temporal Tests"
  [ temporalLogicTests ]
