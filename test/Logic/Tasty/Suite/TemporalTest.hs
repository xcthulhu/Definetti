{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# OPTIONS_GHC -fno-warn-orphans  #-}

module Logic.Tasty.Suite.TemporalTest
  ( temporalTests
  , temporalSemanticsQC
  , TemporalModel
  , TemporalProp
  , before'
  ) where

import Data.List.NonEmpty (NonEmpty)
import Prelude hiding (until)
import Test.QuickCheck (Arbitrary(arbitrary), oneof)
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit ((@?=), testCase)
import Test.Tasty.QuickCheck (testProperty)

import Logic.Propositional
  ( FreeModel
  , FreeVars(Bound)
  , Propositional((:&&:), (:->:), (:||:), Falsum, Not, Proposition,
              Verum)
  )
import Logic.Semantics (ModelSearch(findModel), Semantics((|=)))
import Logic.Temporal (Temporal(Always, Until), before, until)

import Logic.TestAtom (Atom, AtomModel, bound, free)

instance Arbitrary p => Arbitrary (Temporal (Propositional p)) where
  arbitrary = oneof [Until <$> arbitrary <*> arbitrary, Always <$> arbitrary]

type TemporalAtom = FreeVars Char (Temporal (Propositional (Atom Char)))

type TemporalProp = Propositional TemporalAtom

type TemporalModel = FreeModel Char (NonEmpty (AtomModel Char))

findModel' :: TemporalProp -> Maybe TemporalModel
findModel' = findModel

until' :: Propositional (Atom Char) -> Propositional (Atom Char) -> TemporalProp
a `until'` b = Bound <$> (a `until` b)

before' ::
     Propositional (Atom Char) -> Propositional (Atom Char) -> TemporalProp
a `before'` b = Bound <$> (a `before` b)

always' :: Propositional (Atom Char) -> TemporalProp
always' = Proposition . Bound . Always

slowTemporalLogicTests :: TestTree
slowTemporalLogicTests =
  testGroup
    "Temporal Logic Identities"
    [ testCase "No model for `~(Verum until Verum)`" $
      findModel' (Not (Verum `until'` Verum)) @?= Nothing
    , testCase "((Verum until Verum) :->: y) implies y" $
      (|= y) <$> findModel' ((Verum `until'` Verum) :->: y) @?= Just True
    , testCase "Not ((Verum until Verum) :->: y) implies (Not y)" $
      (|= Not y) <$>
      findModel' (Not ((Verum `until'` Verum) :->: y)) @?= Just True
    , testCase
        "Can model `Not (a `until'` (b :->: c)) :&&: (Not (x :->: (Verum `until'` Verum)) :||: Verum)`" $
      let p =
            Not (a `until'` (b :->: c)) :&&:
            (Not (x :->: (Verum `until'` Verum)) :||: Verum)
       in ((|= p) <$> findModel' p @?= Just True)
    , testCase
        "`~a until (a AND b)` AND `~a until (a AND c)` implies `Verum until (b AND c)`" $
      ((|= (Verum `until'` (b :&&: c))) <$>
       findModel' ((Not a `until'` (a :&&: b)) :&&: (Not a `until'` (a :&&: c)))) @?=
      Just True
    , testCase
        "`~a until (a AND b)` AND `~a until (a AND c)` AND `~a until (a AND d)` implies `Verum until (b AND c AND d)`" $
      ((|= (Verum `until'` (b :&&: c :&&: d))) <$>
       findModel'
         ((Not a `until'` (a :&&: b)) :&&: (Not a `until'` (a :&&: c)) :&&:
          (Not a `until'` (a :&&: d)))) @?=
      Just True
    , testCase "`a before b` AND `b before c` implies `a before c`" $
      ((|= (a `before'` c)) <$>
       findModel' ((a `before'` b) :&&: (b `before'` c))) @?=
      Just True
    , testCase "Should not find a model for `Not (Always Verum)`" $
      findModel' (Not (always' Verum)) @?= Nothing
    , testCase "Should not find a model for `Always Falsum`" $
      findModel' (always' Falsum) @?= Nothing
    , testCase "Should not find a model for `Not ((Always Verum) :&&: Verum)`" $
      findModel' (Not (always' Verum) :&&: Verum) @?= Nothing
    , testCase "`a before b` AND `b before c` implies `a before c`" $
      findModel' ((a `before'` b) :&&: (b `before'` c) :&&: (c `before'` a)) @?=
      Nothing
    ]
  where
    x, y :: TemporalProp
    [x, y] = free <$> ['x', 'y']
    [a, b, c, d] = bound <$> ['a', 'b', 'c', 'd']

-- TODO: Since LTL is P-Space complete, we should probably use smaller formulae
temporalSemanticsQC :: TestTree
temporalSemanticsQC =
  testGroup
    "Temporal Semantics Laws"
    [ testProperty
        "Forall f: `fmap (|= f) (findModel f) == fmap (const True) (findModel f)`" $ \f ->
        let m = findModel' f
         in fmap (|= f) m == fmap (const True) m
    ]

temporalTests :: TestTree
temporalTests =
  testGroup "Temporal Logic Tests" [slowTemporalLogicTests, temporalSemanticsQC]
