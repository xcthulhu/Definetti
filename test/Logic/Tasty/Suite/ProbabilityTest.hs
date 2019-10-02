{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# OPTIONS_GHC -fno-warn-orphans  #-}

module Logic.Tasty.Suite.ProbabilityTest
  ( probabilityTests
  ) where

import Prelude hiding (last)

import Control.Exception (throwIO)
import Control.Monad (liftM2, when, forM_)
import Data.List.NonEmpty (last)
import Data.Monoid ((<>))
import Data.Ratio (Rational, (%))
import Data.Typeable (Typeable)
import Text.Printf (printf)

import Logic.Probability
  ( Categorical
  , Probability((:*), (:+), (:-), Const, Pr)
  , ProbabilityInequality((:<), (:<=), (:>), (:>=))
  , pr
  )
import Logic.Probability.Regression (regressProbabilityOrbit)
import Logic.Propositional (Propositional((:&&:), (:->:), (:||:), Not))
import Logic.Semantics
  ( ConstrainedModelSearch
  , ModelSearch(findModel)
  , Semantics((|=))
  )

import Test.QuickCheck (Arbitrary(arbitrary), Gen, oneof, sized, within)
import Test.QuickCheck.Monadic (assert, monadicIO, run)
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit ((@?), (@?=), testCase)
import Test.Tasty.QuickCheck (testProperty)

import Logic.Tasty.Suite.TemporalTest (TemporalModel, TemporalProp, before')
import Logic.TestAtom (Atom, AtomModel, bound)

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
            , liftM2 (:+) subFormula subFormula
            , liftM2 (:-) subFormula subFormula
            ]
        where
          subFormula = sizedProbability (n `div` 3)

instance Arbitrary p => Arbitrary (ProbabilityInequality p) where
  arbitrary =
    oneof
      [ liftM2 (:>) arbitrary arbitrary
      , liftM2 (:<) arbitrary arbitrary
      , liftM2 (:<=) arbitrary arbitrary
      , liftM2 (:>=) arbitrary arbitrary
      ]

newtype UnitIntervalRational =
  UnitIntervalRational Rational
  deriving (Show)

instance Arbitrary UnitIntervalRational where
  arbitrary = do
    x :: Integer <- abs <$> arbitrary
    y :: Integer <- abs <$> arbitrary
    pure . UnitIntervalRational $
      if | x == y -> 1
         | x > y -> y % x
         | otherwise -> x % y

type AtomDist = Categorical (AtomModel Char)

--type TemporalDist = Categorical (TemporalModel)
findModel' :: ProbabilityInequality (Atom Char) -> Maybe AtomDist
findModel' = findModel

type AtomProp = Propositional (Atom Char)

fitProbability ::
     ( Ord p
     , Ord d
     , ConstrainedModelSearch d p Maybe
     , Show p
     , Typeable p
     , Show d
     )
  => Bool
  -> Rational
  -> [Propositional p]
  -> [(Propositional p, Rational)]
  -> IO (Categorical d)
fitProbability debug epsilon laws observations =
  case regressProbabilityOrbit laws observations epsilon of
        Nothing -> fail "regressing probabilities should never fail"
        Just (Left exception) -> throwIO exception
        Just (Right orbit) -> do
          when debug $ print (fmap snd orbit)
          pure . snd $ last orbit

type TemporalDist = Categorical TemporalModel

fitAtomProbability :: [AtomProp] -> [(AtomProp, Rational)] -> IO AtomDist
fitAtomProbability = fitProbability False (1 % 100)

fitTemporalProbability ::
     [TemporalProp] -> [(TemporalProp, Rational)] -> IO TemporalDist
fitTemporalProbability = fitProbability False (1 % 5)

probabilityTheoryTests :: TestTree
probabilityTheoryTests =
  testGroup
    "Probability Theory Identities"
    [ testProperty "Forall x, y, and Pr: Pr (x :&&: y) <= Pr (x :&&: y)" $ \x y ->
        prove $ Pr (x :&&: y) :<= Pr (x :&&: y)
    , testProperty
        "Forall x, y, and Pr: Pr x :+ Pr y <= Pr (x :||: y) :+ Pr (x :&&: y)" $ \x y ->
        prove $ (Pr x :+ Pr y) :> (Pr (x :||: y) :+ Pr (x :&&: y))
    , testProperty
        "Forall x, y, and Pr: Pr x :+ Pr y >= Pr (x :||: y) :+ Pr (x :&&: y)" $ \x y ->
        prove $ (Pr x :+ Pr y) :>= (Pr (x :||: y) :+ Pr (x :&&: y))
    , testCase "Exists Pr s.t. Pr a :+ Pr b > Pr (a :||: b)" $
      ((True @?=) . someModel) ((Pr a :+ Pr b) :> Pr (a :||: b))
    , testCase "Exists Pr s.t. 0.5 > Pr (a :||: b)" $
      ((True @?=) . someModel) (Const 0.5 :> Pr (a :||: b))
    , testProperty "Forall x and Pr: 1 <= Pr x :+ Pr (Not x)" $ \x ->
        prove $ Const 1 :<= (Pr x :+ Pr (Not x))
    , testProperty "Forall x and Pr: Pr x :+ Pr (Not x) <= 1" $ \x ->
        prove $ (Pr x :+ Pr (Not x)) :<= Const 1
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
        prove (Const (-2) :<= Pr x)
    , testProperty "Forall x and Pr: 3 * Pr x <= 4 * Pr x" $ \x ->
        prove ((3 :* Pr x) :<= (4 :* Pr x))
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
    prove (x :< y) = noModel (x :>= y)
    prove (x :<= y) = noModel (x :> y)
    prove (x :> y) = noModel (x :<= y)
    prove (x :>= y) = noModel (x :< y)
    someModel p = ((|= p) <$> findModel' p) == Just True

probabilityInequalitySemanticsQC :: TestTree
probabilityInequalitySemanticsQC =
  testGroup
    "Probability Semantics Laws"
    [ testProperty
        ("Forall f: `fmap (|= f) (findModel f)" <>
         " == fmap (const True) (findModel f)`") $
      within 10000000 $ \f ->
        let m = findModel' f
         in fmap (|= f) m == fmap (const True) m
    ]


assertApproxEquals :: Rational -> Rational -> Rational -> IO ()
assertApproxEquals actual expected eps =
  (abs (actual - expected) < eps) @?
  printf
    "Expected %.3f to be within %f of %.3f"
    (fromRational actual :: Float)
    (fromRational eps :: Float)
    (fromRational expected :: Float)

regressingProbabilityTests :: TestTree
regressingProbabilityTests =
  testGroup
    "Tests for fitting probabilities"
    [ testCase "Fit a fair coin with P(Heads) = 1/2 properly" $ do
        model <- fitAtomProbability [] [(a, 1 % 2)]
        pr model (Pr a) @?= 1 % 2
    , testCase "Fit a coin with P(Heads) = 1/3 properly" $ do
        model <- fitAtomProbability [] [(a, 1 % 3)]
        pr model (Pr a) @?= 1 % 3
    , testCase "Fit two coins with P(Heads 1) = 1/2 and P(Heads 2) = 1/3" $ do
        model <- fitAtomProbability [] [(a, 1 % 2), (b, 1 % 3)]
        assertApproxEquals (pr model (Pr a)) (1 % 2) (1 % 1000)
        assertApproxEquals (pr model (Pr b)) (1 % 3) (1 % 1000)
    , testCase "Fit nonsense coin with P(Heads) = 2/3 P(Tails) = 2/3" $ do
        model <- fitAtomProbability [] [(a, 2 % 3), (Not a, 2 % 3)]
        pr model (Pr a) @?= 1 % 2
    , testCase "Fit a nonsense coin with P(Heads) = 1/4 P(Tails) = 1/4" $ do
        model <- fitAtomProbability [] [(a, 1 % 4), (Not a, 1 % 4)]
        pr model (Pr a) @?= 1 % 2
    , testProperty "Fit a random weighted coin" $ \(UnitIntervalRational p) ->
        monadicIO $ do
          model <- run $ fitAtomProbability [] [(a, p)]
          assert $ pr model (Pr a) == p
    ]
  where
    [a, b] = bound <$> ['a', 'b']

regressingTemporalProbabilityTests :: TestTree
regressingTemporalProbabilityTests =
  testGroup
    "Temporal Logic Probability Regression"
    [ testCase "Fit A>B,B>C,C>A @ 90% all (should be 66.666%)" $
      checkCycle 3 (9%10) (3 % 100)
    , testCase "Fit 4-cycle @ 99.9% all (should be 75%)" $
      checkCycle 4 (999%1000) (3 % 100)
    , testCase "Fit 5-cycle @ 99% all (should be 80%)" $
      checkCycle 5 (99%100) (3 % 100)
    , testCase "Fit 6-cycle @ 90% all" $
      checkCycle 6 (9%10) (3 % 100)
    , testCase "Fit 7-cycle @ 90% all" $
      checkCycle 7 (9%10) (3 % 100)
    , testCase "Fit 8-cycle @ 90% all" $
      checkCycle 8 (9%10) (3 % 100)
    ]
  where
    checkCycle n p delta = do
      let vars = bound <$> take (fromIntegral n) ['a'..]
          propositions = zipWith before' vars (tail $ cycle vars)
      model <- fitTemporalProbability [] [(prop, p) | prop <- propositions]
      forM_ propositions $ \prop ->
        assertApproxEquals (pr model (Pr prop)) ((n-1) % n) delta


probabilityTests :: TestTree
probabilityTests =
  testGroup
    "Probability Tests"
    [ probabilityTheoryTests
    , probabilityInequalitySemanticsQC
    , regressingProbabilityTests
    , regressingTemporalProbabilityTests
    ]
