{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TupleSections         #-}
{-# OPTIONS_GHC -fno-warn-orphans  #-}

module Logic.Tasty.Suite.LinearProgrammingTest
  ( linearProgrammingTests
  )
where

import           Prelude                   hiding (sequence)

import           Control.Monad.Trans.Maybe (runMaybeT)
import qualified Data.Map                  as Map
import           Data.Ratio                ((%))
import qualified Data.Set                  as Set
import           Logic.LinearProgramming   (LinearInequality ((:<:), (:<=:)),
                                            SumPlusConstant ((:+:)))


import           Test.Tasty                (TestTree, testGroup)
import           Test.Tasty.HUnit          (testCase, (@?=))

import           Logic.Propositional       (ConstrainedModelSearch (findConstrainedModel),
                                            Literal (Pos))
import           Logic.Semantics           (Semantics ((|=)))


findConstrainedModel'
  :: Set.Set (Literal (LinearInequality Rational))
  -> IO (Maybe (Map.Map String Rational))
findConstrainedModel' = runMaybeT . findConstrainedModel

linearProgrammingTests :: TestTree
linearProgrammingTests = testGroup
  "Linear programming tests"
  [ testCase "Exists a model s.t. 1/2 X <= X" $ do
      let inequality = [(1 % 2, "X")] :+: 0 :<=: [(1, "X")] :+: 0
      model <- findConstrainedModel' $ Set.fromList [Pos inequality]
      (|= inequality) <$> model @?= Just True

  , testCase "Exists a model s.t. X == 0" $ do
      let lt0 = [(1, "X")] :+: 0 :<=: [] :+: 0
          gt0 = [] :+: 0 :<=: [(1, "X")] :+: 0
          gt1 = [] :+: 1 :<=: [(1 :: Rational, "X")] :+: 0
      model <- findConstrainedModel' $ Set.fromList [ Pos lt0, Pos gt0 ]
      (|= lt0) <$> model @?= Just True
      (|= gt0) <$> model @?= Just True
      (|= gt1) <$> model @?= Just False

  , testCase "Exists a model s.t. 2 X <= X" $ do
      let inequality = [(2, "X")] :+: 0 :<=: [(1, "X")] :+: 0
          gt0 = [] :+: 0 :<: [(1, "X")] :+: (0 :: Rational)
      model <- findConstrainedModel' $ Set.fromList [ Pos inequality ]
      (|= inequality) <$> model @?= Just True
      (|= gt0) <$> model @?= Just False

  , testCase "Exists a model s.t. A < B && B < C" $ do
      let aLTb = [(1, "A")] :+: 0 :<: [(1, "B")] :+: 0
          bLTc = [(1, "B")] :+: 0 :<: [(1, "C")] :+: 0
          aLTc = [(1, "A")] :+: 0 :<: [(1, "C")] :+: (0 :: Rational)
          cLEa = [(1, "C")] :+: 0 :<=: [(1, "A")] :+: (0 :: Rational)
      model <- findConstrainedModel' $ Set.fromList [ Pos aLTb, Pos bLTc ]
      (|= aLTc) <$> model @?= Just True
      (|= cLEa) <$> model @?= Just False
  ]
