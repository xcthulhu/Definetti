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
import           Logic.Probability     (Probability (..),
                                        ProbabilityInequality (..))
import           Logic.Propositional   (ConjClause, Literal (Neg, Pos),
                                        Propositional (..))
import           Logic.Semantics       (ModelSearch (findModel),
                                        Semantics ((|=)))
import           Test.QuickCheck       (Arbitrary (arbitrary), Gen, oneof,
                                        sized)
import           Test.Tasty            (TestTree, testGroup)
import           Test.Tasty.HUnit      (testCase, (@?=))
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

instance Arbitrary p => Arbitrary (Probability p) where
  arbitrary = sized sizedProbability
    where
      sizedProbability :: Arbitrary p => Int -> Gen (Probability p)
      sizedProbability n
        | n <= 0 = fmap Pr arbitrary
        | otherwise =
          oneof [ fmap Pr arbitrary
                , fmap Const arbitrary
                , liftM2 (:+) halfSizeSubFormula halfSizeSubFormula ]
        where
          halfSizeSubFormula = sizedProbability (n `div` 2)

instance Arbitrary p => Arbitrary (ProbabilityInequality p) where
  arbitrary = oneof [ liftM2 (:>) arbitrary arbitrary
                    , liftM2 (:<) arbitrary arbitrary
                    , liftM2 (:<=) arbitrary arbitrary
                    , liftM2 (:>=) arbitrary arbitrary
                    ]

instance Ord p => Semantics (Data.Set.Set p) p where
  (|=) = flip Data.Set.member

-- | ModelSearch for conjunctions of free boolean variables
-- If two of the variables in the conjunction contradict, fail (modeled with Control.Applicative.empty)
-- Otherwise return the set of positive variables
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
propositionalIdentitiesHUnit = testGroup
  "Simple Model Search Tests"
  [ testCase "No m s.t. `m |= (Verum :->: Falsum)`"
  $   findModel' (Verum :->: Falsum) @?= Nothing
  , testCase "No m s.t. `m |= Falsum`" $ findModel' Falsum @?= Nothing
  , testCase "Exists m s.t. `m |= Verum` "
    $ ((True @?=) . Data.Maybe.isJust . findModel') Verum
  , testCase "Exists m s.t. `m |= a`"
    $ ((True @?=) . Data.Maybe.isJust . findModel') a
  , testCase "Exists m s.t. `(m |= Not a) && not (m |= a)`"
    $ fmap (|= a) (findModel' (Not a)) @?= Just False
  , testCase "Exists m s.t. `(m |= (a :||: b)) && ((m |= a) || (m |= b))`"
    $ let searchResult = findModel' (a :||: b)
      in  (True @?=)
            (  (fmap (|= a) searchResult == Just True)
            || (fmap (|= b) searchResult == Just True)
            )
  , testCase
      (  "Exists m s.t. `(m |= Not (a :||: b)) "
      <> "&& not (m |= a) && not (m |= b)`"
      )
    $ let searchResult = findModel' (Not (a :||: b))
      in  (True @?=)
            (  (fmap (|= a) searchResult == Just False)
            && (fmap (|= b) searchResult == Just False)
            )
  , testCase
      (  "Exists m s.t. `m |= Not (p && q) "
      <> "&& (not (m |= a) || not (m |= b))`"
      )
    $ let searchResult = findModel' (Not (a :&&: b))
      in  (True @?=)
            (  (fmap (|= a) searchResult == Just False)
            || (fmap (|= b) searchResult == Just False)
            )
  , testCase
      (  "Exists m s.t. `(m |= (a :&&: (b :||: c))) "
      <> "&& (m |= (a :&&: b) || m |= (a :&&: c))`"
      )
    $ let searchResult = findModel' (a :&&: (b :||: c))
      in  (True @?=)
            (  (fmap (|= (a :&&: b)) searchResult == Just True)
            || (fmap (|= (a :&&: c)) searchResult == Just True) )
  ]
 where
  a = Proposition 'a'
  b = Proposition 'b'
  c = Proposition 'c'
  findModel' :: Propositional Char -> Maybe (Data.Set.Set Char)
  findModel' = findModel

propositionalSemanticsQC :: TestTree
propositionalSemanticsQC = testGroup
  "Propositional Semantics Laws"
  [ testProperty
        (  "Forall f: `fmap (|= f) (findModel f)"
        <> " == fmap (const True) (findModel f)`"
        )
      $ \f -> fmap (|= f) (findModel' f) == fmap (const True) (findModel' f)
  ]
 where
  findModel' :: Propositional Char -> Maybe (Data.Set.Set Char)
  findModel' = findModel

probabilityTheoryQC :: TestTree
probabilityTheoryQC = testGroup
  "Probability Theory Identities"
  [ testProperty "Forall x, y, and Pr: Pr (x :&&: y) <= Pr (x :&&: y)"
    $ \x y -> noModel $ Pr (x :&&: y) :> Pr (x :&&: y)
  , testProperty
      "Forall x, y, and Pr: Pr x :+ Pr y <= Pr (x :||: y) :+ Pr (x :&&: y)"
    $ \x y -> noModel $ (Pr x :+ Pr y) :> (Pr (x :||: y) :+ Pr (x :&&: y))
  , testProperty
      "Forall x, y, and Pr: Pr x :+ Pr y >= Pr (x :||: y) :+ Pr (x :&&: y)"
    $ \x y -> noModel $ (Pr x :+ Pr y) :< (Pr (x :||: y) :+ Pr (x :&&: y))
  , testCase "Exists Pr s.t. Pr a :+ Pr b > Pr (a :||: b)"
    $ ((True @?=) . someModel) ((Pr a :+ Pr b) :> Pr (a :||: b))
  , testCase "Exists Pr s.t. 0.5 > Pr (a :||: b)"
    $ ((True @?=) . someModel) (Const 0.5 :> Pr (a :||: b))
  , testProperty "Forall x and Pr: 1 <= Pr x :+ Pr (Not x)"
    $ \x -> noModel $ Const 1 :> (Pr x :+ Pr (Not x))
  , testProperty "Forall x and Pr: Pr x :+ Pr (Not x) <= 1"
    $ \x -> noModel $ (Pr x :+ Pr (Not x)) :> Const 1
  , testProperty
      (  "Forall x, y, z, and Pr:"
      <> " 2*Pr x <="
      <> " Pr (y :->: (z :&&: x))"
      <> " :+ Pr (z :->: (y :&&: x))"
      <> " :+ Pr ((y :&&: x) :||: (z :&&: x))"
      )
    $ \x y z -> noModel
          $  (2 :* Pr x) :> (   Pr (y :->: (z :&&: x))
                             :+ Pr (z :->: (y :&&: x))
                             :+ Pr ((y :&&: x) :||: (z :&&: x)))
  , testProperty "Forall x and Pr: -2 <= Pr x" $
    \x -> noModel (Const (-2) :> Pr x)
  , testProperty "Forall x and Pr: 3 * Pr x <= 4 * Pr x" $
    \x -> noModel ((3 :* Pr x) :> (4 :* Pr x))
  , testCase "Exists a model where 5 > 0" $
    True @?= someModel (Const 5 :> Const 0)
  , testCase "For all models: not (0 > 5)" $
    True @?= noModel (Const 0 :> Const 5)
  , testCase "For all models: not (1 < 0)" $
    True @?= noModel (Const 1 :< Const 0)
  , testCase "For all models: not (1 < 1)" $
    True @?= noModel (Const 1 :< Const 1)
  , testCase "For all models: not (1 <= 0)" $
    True @?= noModel (Const 1 :<= Const 0)
  , testCase "For all models: not (-4.2 <= -4.8)" $
    True @?= noModel (Const (-4.3) :<= Const (-4.8))
  , testCase "For all models: not (19 < -3)" $
    True @?= noModel (Const 19 :< Const (-3))
  , testCase "For all models: not (19 <= -3)" $
    True @?= noModel (Const 19 :<= Const (-3))
  ]
 where
  a = Proposition 'a'
  b = Proposition 'b'
  findModel' :: ProbabilityInequality Char -> Maybe (Data.Set.Set Char)
  findModel' = findModel
  noModel    = Data.Maybe.isNothing . findModel'
  someModel  = Data.Maybe.isJust . findModel'

probabilityInequalitySemanticsQC :: TestTree
probabilityInequalitySemanticsQC = testGroup
  "Probability Semantics Laws"
  [ testProperty
        (  "Forall f: `fmap (|= f) (findModel f)"
        <> " == fmap (const True) (findModel f)`"
        )
      $ \f -> fmap (|= f) (findModel' f) == fmap (const True) (findModel' f)
  ]
 where
  findModel' :: ProbabilityInequality Char -> Maybe (Data.Set.Set Char)
  findModel' = findModel

propositionalTests :: TestTree
propositionalTests = testGroup
  "Propositional Tests"
  [ propositionalIdentitiesHUnit
  , propositionalSemanticsQC
  , probabilityTheoryQC
  , probabilityInequalitySemanticsQC
  ]
