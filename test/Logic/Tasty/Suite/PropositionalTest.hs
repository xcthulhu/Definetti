{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# OPTIONS_GHC -fno-warn-orphans  #-}

module Logic.Tasty.Suite.PropositionalTest (propositionalTests)
where

import qualified Data.Maybe            (isJust)
import           Data.Monoid           ((<>))
import           Test.Tasty            (TestTree, testGroup)
import           Test.Tasty.HUnit      (testCase, (@?), (@?=))
import           Test.Tasty.QuickCheck (testProperty)

import           Logic.Propositional   (Propositional ((:&&:), (:->:), (:||:), Falsum, Not, Verum))
import           Logic.Semantics       (ModelSearch (findModel),
                                        Semantics ((|=)))
import           Logic.TestAtom


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
  [a,b,c] = bound <$> ['a', 'b', 'c']

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
