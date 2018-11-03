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
  , testCase "Exists a model s.t. 1 < X && X < 2" $ do
      let c1 = []         :+: 0 :<: [(1, "X")]     :+: 0
          c2 = [(1, "X")] :+: 0 :<: []             :+: 2
      model <- findConstrainedModel' $ Set.fromList [ Pos c1, Pos c2 ]
      (|= c1) <$> model @?= Just True
      (|= c2) <$> model @?= Just True
  , testCase "Exists a model s.t. 1 < X && X < 2" $ do
      let c1 = []         :+: 0 :<: [(1, "X")]     :+: 0
          c2 = [(1, "X")] :+: 0 :<: []             :+: 1
      model <- findConstrainedModel' $ Set.fromList [ Pos c1, Pos c2 ]
      (|= c1) <$> model @?= Just True
      (|= c2) <$> model @?= Just True
  , testCase "Exists a model s.t. 0 < X && X < 1 && 0 < Y && Y < 1/2 X" $ do
      let c1 = []         :+: 0 :<: [(1, "X")]     :+: 0
          c2 = [(1, "X")] :+: 0 :<: []             :+: 1
          c3 = []         :+: 0 :<: [(1, "Y")]     :+: 0
          c4 = [(1, "Y")] :+: 0 :<: [(1 % 2, "X")] :+: 0
      model <- findConstrainedModel' $ Set.fromList [ Pos c1, Pos c2, Pos c3, Pos c4 ]
      (|= c1) <$> model @?= Just True
      (|= c2) <$> model @?= Just True
      (|= c3) <$> model @?= Just True
      (|= c4) <$> model @?= Just True
  ]
