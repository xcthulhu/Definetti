{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# OPTIONS_GHC -fno-warn-orphans  #-}

module Logic.Tasty.Suite.LinearProgrammingTest (linearProgrammingTests)
where

import           Prelude               hiding (until)
import           Test.Tasty            (TestTree, testGroup)
import           Test.Tasty.HUnit      (testCase, (@?=))

import Logic.LinearProgramming (SumPlusConstant ((:+:)))


basicLinearProgrammingTests :: TestTree
basicLinearProgrammingTests = testGroup 
  "Basic Tests" 
  [
    testCase "1/2 X <= X" $ 
      [(1 :: Int, "X")] :+: 0 @?= [(1, "X")] :+: 0
  ]

linearProgrammingTests :: TestTree
linearProgrammingTests = testGroup
  "Linear Programming Tests"
    [
      basicLinearProgrammingTests
    ]
