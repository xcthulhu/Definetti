{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables   #-}

module Logic.PropositionalTest (propositionalTests)
where

import           Control.Applicative   (Alternative, empty, pure)
import           Control.Monad         (liftM2)
import qualified Data.Maybe            (isJust, isNothing)
import           Data.Monoid           ((<>))
import qualified Data.Set              (Set, filter, map, member)
import           Test.QuickCheck       (Arbitrary (arbitrary), Gen, oneof,
                                        sized)
import           Test.Tasty            (TestTree, testGroup)
import           Test.Tasty.HUnit      (testCase, (@?), (@?=))
import           Test.Tasty.QuickCheck (testProperty)

import           Logic.Probability     (Probability ((:*), (:+), Const, Pr), ProbabilityInequality ((:<), (:<=), (:>), (:>=)))
import           Logic.Propositional   (FreeVars (Bound, Free),
                                        Literal (Neg, Pos),
                                        Propositional ((:&&:), (:->:), (:||:), Falsum, Not, Proposition, Verum))
import           Logic.Semantics       (ConstrainedModelSearch (findConstrainedModel),
                                        ModelSearch (findModel),
                                        Semantics ((|=)))

newtype Urelement a = Urelement a deriving (Ord, Eq, Show)

type Atom a = FreeVars (Urelement a)

bound :: a -> Atom a
bound = Bound . Urelement

instance Arbitrary p => Arbitrary (Propositional (Atom p)) where
  arbitrary = sized sizedArbitraryProposition
    where
      -- | Create a propositional formula that has at most depth n
      sizedArbitraryProposition :: Arbitrary p => Int -> Gen (Propositional (Atom p))
      sizedArbitraryProposition n
        | n <= 0    = oneof atomic
        | otherwise = oneof $ atomic <>
          [ liftM2 (:&&:) halfSizeSubFormula halfSizeSubFormula
          , liftM2 (:||:) halfSizeSubFormula halfSizeSubFormula
          , liftM2 (:->:) halfSizeSubFormula halfSizeSubFormula
          , Not <$> sizedArbitraryProposition (n - 1)
          , pure Verum
          , pure Falsum
          ]
        where
          atomic =
            [ Proposition . bound <$> arbitrary
            , Proposition . Free <$> arbitrary
            ]
          halfSizeSubFormula = sizedArbitraryProposition (n `div` 2)

instance Arbitrary p => Arbitrary (Probability (Atom p)) where
  arbitrary = sized sizedProbability
    where
      sizedProbability :: Arbitrary p => Int -> Gen (Probability (Atom p))
      sizedProbability n
        | n <= 0 = Pr <$> arbitrary
        | otherwise =
          oneof [ Pr <$> arbitrary
                , Const <$> arbitrary
                , liftM2 (:+) halfSizeSubFormula halfSizeSubFormula ]
        where
          halfSizeSubFormula = sizedProbability (n `div` 2)

instance Arbitrary p => Arbitrary (ProbabilityInequality (Atom p)) where
  arbitrary = oneof [ liftM2 (:>) arbitrary arbitrary
                    , liftM2 (:<) arbitrary arbitrary
                    , liftM2 (:<=) arbitrary arbitrary
                    , liftM2 (:>=) arbitrary arbitrary
                    ]

instance Ord p => Semantics (Data.Set.Set (Atom p)) (Atom p) where
  (|=) = flip Data.Set.member

-- | ModelSearch for conjunctions of free boolean variables
-- If two of the variables in the conjunction contradict, fail (modeled with Control.Applicative.empty)
-- Otherwise return the set of positive variables
instance (Ord p, Alternative f) => ConstrainedModelSearch f (Data.Set.Set (Atom p)) (Atom p)
  where
    findConstrainedModel clause =
      if any ((`Data.Set.member` clause) . neg) clause
      then empty
      else pure . Data.Set.map project . Data.Set.filter positive $ clause
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
    $ ((@? "Could not find model for verum") . Data.Maybe.isJust . findModel') Verum
  , testCase "Exists m s.t. `m |= a`"
    $ ((@? "Could not find model for naked atom 'a'") . Data.Maybe.isJust . findModel') a
  , testCase "Exists m s.t. `(m |= Not a) && not (m |= a)`"
    $ (|= a) <$> findModel' (Not a) @?= Just False
  , testCase "Exists m s.t. `(m |= (a :||: b)) && ((m |= a) || (m |= b))`"
    $ let searchResult = findModel' (a :||: b)
      in (  (fmap (|= a) searchResult == Just True)
         || (fmap (|= b) searchResult == Just True)
         ) @? "Could not find a model for `a :||: b`"
  , testCase
      (  "Exists m s.t. `(m |= Not (a :||: b)) "
      <> "&& not (m |= a) && not (m |= b)`"
      )
    $ let searchResult = findModel' (Not (a :||: b))
      in (  (fmap (|= a) searchResult == Just False)
         && (fmap (|= b) searchResult == Just False)
         ) @? "Could not find a model for `Not (a :||: b)"
  , testCase
      (  "Exists m s.t. `m |= Not (p && q) "
      <> "&& (not (m |= a) || not (m |= b))`"
      )
    $ let searchResult = findModel' (Not (a :&&: b))
      in (  (fmap (|= a) searchResult == Just False)
         || (fmap (|= b) searchResult == Just False)
         ) @? "Could not find a model for `Not (a :&&: b)`"
  , testCase
      (  "Exists m s.t. `(m |= (a :&&: (b :||: c))) "
      <> "&& (m |= (a :&&: b) || m |= (a :&&: c))`"
      )
    $ let searchResult = findModel' (a :&&: (b :||: c))
      in  (  (fmap (|= (a :&&: b)) searchResult == Just True)
          || (fmap (|= (a :&&: c)) searchResult == Just True)
          ) @? "Could not find a model for `a :&&: (b :||: c)`"
  ]
 where
  a = Proposition . bound $ 'a'
  b = Proposition . bound $ 'b'
  c = Proposition . bound $ 'c'
  findModel' :: Propositional (Atom Char) -> Maybe (Data.Set.Set (Atom Char))
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
  findModel' :: Propositional (Atom Char) -> Maybe (Data.Set.Set (Atom Char))
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
  a = Proposition . bound $ 'a'
  b = Proposition . bound $ 'b'
  findModel' :: ProbabilityInequality (Atom Char) -> Maybe (Data.Set.Set (Atom Char))
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
  findModel' :: ProbabilityInequality (Atom Char) -> Maybe (Data.Set.Set (Atom Char))
  findModel' = findModel

propositionalTests :: TestTree
propositionalTests = testGroup
  "Propositional Tests"
  [ propositionalIdentitiesHUnit
  , propositionalSemanticsQC
  , probabilityTheoryQC
  , probabilityInequalitySemanticsQC
  ]
