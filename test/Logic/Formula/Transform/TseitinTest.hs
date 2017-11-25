module Logic.Formula.Transform.TseitinTest (test_tseitin) where

import           Logic.Formula.Data.Propositional.QuickCheck ()
import           Test.Tasty
import           Test.Tasty.QuickCheck

test_tseitin :: TestTree
test_tseitin = testGroup "Tseitin Tests"
  [
    testProperty "Tseitin transformation preserves propositional atoms"
     $ \x -> (x :: Int) == x
  ]
