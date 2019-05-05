{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# OPTIONS_GHC -fno-warn-orphans  #-}

module Logic.Tasty.Suite.ProbabilityTest
  ( probabilityTests
  ) where

import           Control.Monad         (liftM2)
import           Data.Monoid           ((<>))
import           Test.QuickCheck       (Arbitrary (arbitrary), Gen, oneof,
                                        sized, within)
import           Test.Tasty            (TestTree, testGroup)
import           Test.Tasty.HUnit      (testCase, (@?), (@?=))
import           Test.Tasty.QuickCheck (testProperty)

import           Logic.Probability     (Categorical,
                                        Probability ((:*), (:+), Const, Pr, (:-)),
                                        ProbabilityInequality ((:<), (:<=), (:>), (:>=)))
import           Logic.Propositional   (Propositional ((:&&:), (:->:), (:||:), Not))
import           Logic.Semantics       (ModelSearch (findModel),
                                        Semantics ((|=)))

import           Logic.TestAtom        (Atom, AtomModel, bound)

instance Arbitrary p => Arbitrary (Probability p) where
  arbitrary = sized sizedProbability
    where
      sizedProbability :: Arbitrary p => Int -> Gen (Probability p)
      sizedProbability n
        | n <= 0 = Pr <$> arbitrary
        | otherwise =
          oneof
            [ Pr <$> arbitrary
            , Const <$> arbitrary
            , liftM2 (:*) arbitrary (sizedProbability (n - 1))
            , liftM2 (:+) halfSizeSubFormula halfSizeSubFormula
            , liftM2 (:-) halfSizeSubFormula halfSizeSubFormula
            ]
        where
          halfSizeSubFormula = sizedProbability (n `div` 2)

instance Arbitrary p => Arbitrary (ProbabilityInequality p) where
  arbitrary =
    oneof
      [ liftM2 (:>) arbitrary arbitrary
      , liftM2 (:<) arbitrary arbitrary
      , liftM2 (:<=) arbitrary arbitrary
      , liftM2 (:>=) arbitrary arbitrary
      ]

findModel' ::
     ProbabilityInequality (Atom Char) -> Maybe (Categorical (AtomModel Char))
findModel' = findModel

probabilityTheoryQC :: TestTree
probabilityTheoryQC =
  testGroup
    "Probability Theory Identities"
    [ testProperty "Forall x, y, and Pr: Pr (x :&&: y) <= Pr (x :&&: y)" $ \x y ->
        noModel $ Pr (x :&&: y) :> Pr (x :&&: y)
    , testProperty
        "Forall x, y, and Pr: Pr x :+ Pr y <= Pr (x :||: y) :+ Pr (x :&&: y)" $ \x y ->
        noModel $ (Pr x :+ Pr y) :> (Pr (x :||: y) :+ Pr (x :&&: y))
    , testProperty
        "Forall x, y, and Pr: Pr x :+ Pr y >= Pr (x :||: y) :+ Pr (x :&&: y)" $ \x y ->
        noModel $ (Pr x :+ Pr y) :< (Pr (x :||: y) :+ Pr (x :&&: y))
    , testCase "Exists Pr s.t. Pr a :+ Pr b > Pr (a :||: b)" $
      ((True @?=) . someModel) ((Pr a :+ Pr b) :> Pr (a :||: b))
    , testCase "Exists Pr s.t. 0.5 > Pr (a :||: b)" $
      ((True @?=) . someModel) (Const 0.5 :> Pr (a :||: b))
    , testProperty "Forall x and Pr: 1 <= Pr x :+ Pr (Not x)" $ \x ->
        noModel $ Const 1 :> (Pr x :+ Pr (Not x))
    , testProperty "Forall x and Pr: Pr x :+ Pr (Not x) <= 1" $ \x ->
        noModel $ (Pr x :+ Pr (Not x)) :> Const 1
    , testProperty
        (unwords
           [ "Forall x, y, z, and Pr:"
           , "2*Pr x <="
           , "Pr (y :->: (z :&&: x))"
           , ":+ Pr (z :->: (y :&&: x))"
           , " :+ Pr ((y :&&: x) :||: (z :&&: x))"
           ]) $ \x y z ->
        noModel $ (2 :* Pr x) :>
        (Pr (y :->: (z :&&: x)) :+ Pr (z :->: (y :&&: x)) :+
         Pr ((y :&&: x) :||: (z :&&: x)))
    , testProperty "Forall x and Pr: -2 <= Pr x" $ \x ->
        noModel (Const (-2) :> Pr x)
    , testProperty "Forall x and Pr: 3 * Pr x <= 4 * Pr x" $ \x ->
        noModel ((3 :* Pr x) :> (4 :* Pr x))
    , testCase "Exists a model where 5 > 0" $ someModel (Const 5 :> Const 0) @?
      "Could not find a model for 5 > 0"
    , testCase "For all models: not (0 > 5)" $ findModel' (Const 0 :> Const 5) @?=
      Nothing
    , testCase "For all models: not (1 < 0)" $ findModel' (Const 1 :< Const 0) @?=
      Nothing
    , testCase "For all models: not (1 < 1)" $ findModel' (Const 1 :< Const 1) @?=
      Nothing
    , testCase "For all models: not (1 <= 0)" $ findModel' (Const 1 :<= Const 0) @?=
      Nothing
    , testCase "For all models: not (-4.2 <= -4.8)" $
      findModel' (Const (-4.3) :<= Const (-4.8)) @?=
      Nothing
    , testCase "For all models: not (19 < -3)" $
      findModel' (Const 19 :< Const (-3)) @?=
      Nothing
    , testCase "For all models: not (19 <= -3)" $
      findModel' (Const 19 :<= Const (-3)) @?=
      Nothing
    , testCase "Exists a model where (-1 * a < b)" $
      let p = ((-1) :* Pr a) :< Pr b
       in (|= p) <$> findModel' p @?= Just True
    ]
  where
    [a, b] = bound <$> ['a', 'b']
    noModel = (Nothing ==) . findModel'
    someModel p = ((|= p) <$> findModel' p) == Just True

probabilityInequalitySemanticsQC :: TestTree
probabilityInequalitySemanticsQC =
  testGroup
    "Probability Semantics Laws"
    [
      testProperty
        ("Forall f: `fmap (|= f) (findModel f)" <>
         " == fmap (const True) (findModel f)`") $ within 10000000 $
        \f ->
        let m = findModel' f
         in fmap (|= f) m == fmap (const True) m
    ]

probabilityTests :: TestTree
probabilityTests =
  testGroup
    "Propositional Tests"
    [probabilityTheoryQC, probabilityInequalitySemanticsQC]
