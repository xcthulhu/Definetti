{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# OPTIONS_GHC -fno-warn-orphans  #-}

module Logic.PropositionalTest (propositionalTests, Atom, AtomModel, bound)
where

import           Control.Applicative   (Alternative, empty, pure)
import           Control.Monad         (liftM2)
import qualified Data.Maybe            (isJust)
import           Data.Monoid           ((<>))
import qualified Data.Set              (Set, filter, map, member)
import           Test.QuickCheck       (Arbitrary (arbitrary), Gen, oneof,
                                        sized)
import           Test.Tasty            (TestTree, testGroup)
import           Test.Tasty.HUnit      (testCase, (@?), (@?=))
import           Test.Tasty.QuickCheck (testProperty)

import           Logic.Propositional   (FreeVars (Bound, Free),
                                        Literal (Neg, Pos),
                                        Propositional ((:&&:), (:->:), (:||:), Falsum, Not, Proposition, Verum))
import           Logic.Semantics       (ConstrainedModelSearch (findConstrainedModel),
                                        ModelSearch (findModel),
                                        Semantics ((|=)))


newtype Urelement a = Urelement a deriving (Ord, Eq, Show)

type Atom a = FreeVars Char (Urelement a)

bound :: a -> Atom a
bound = Bound . Urelement

type AtomModel p = Data.Set.Set (Atom p)

instance Arbitrary p => Arbitrary (Atom p) where
  arbitrary = oneof [ bound <$> arbitrary
                    , Free <$> arbitrary
                    ]

instance Arbitrary p => Arbitrary (Propositional p) where
  arbitrary = sized sizedArbitraryProposition where
    -- | Create a propositional formula that has at most depth n
    sizedArbitraryProposition :: Arbitrary p => Int -> Gen (Propositional p)
    sizedArbitraryProposition n
      | n <= 0    = atomic
      | otherwise = oneof
        [ atomic
        , liftM2 (:&&:) halfSizeSubFormula halfSizeSubFormula
        , liftM2 (:||:) halfSizeSubFormula halfSizeSubFormula
        , liftM2 (:->:) halfSizeSubFormula halfSizeSubFormula
        , Not <$> sizedArbitraryProposition (n - 1)
        , pure Verum
        , pure Falsum
        ]
      where
        atomic = Proposition <$> arbitrary
        halfSizeSubFormula = sizedArbitraryProposition (n `div` 2)

instance Ord p => Semantics (AtomModel p) (Atom p) where
  (|=) = flip Data.Set.member

-- | ModelSearch for conjunctions of free boolean variables
-- If two of the variables in the conjunction contradict, fail (modeled with Control.Applicative.empty)
-- Otherwise return the set of positive variables
instance (Ord p, Alternative f) => ConstrainedModelSearch (AtomModel p) (Atom p) f
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

findModel' :: Propositional (Atom Char) -> Maybe (AtomModel Char)
findModel' = findModel

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

propositionalSemanticsQC :: TestTree
propositionalSemanticsQC = testGroup
  "Propositional Semantics Laws"
  [ testProperty
        (  "Forall f: `fmap (|= f) (findModel f)"
        <> " == fmap (const True) (findModel f)`"
        )
      $ \f -> let m = findModel' f
              in fmap (|= f) m == fmap (const True) m
  ]

propositionalTests :: TestTree
propositionalTests = testGroup
  "Propositional Tests"
  [ propositionalIdentitiesHUnit
  , propositionalSemanticsQC
  ]
