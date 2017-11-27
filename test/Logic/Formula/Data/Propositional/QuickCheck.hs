{-# OPTIONS_GHC -fno-warn-orphans #-}
module Logic.Formula.Data.Propositional.QuickCheck () where
import           Control.Monad                    (liftM2)
import           Logic.Formula.Data.Propositional
import           Test.QuickCheck

instance Arbitrary a => Arbitrary (Propositional a) where
  arbitrary = sized sizedArbitraryProposition
    where
      -- | Create a propositional formula that has at most depth n
      sizedArbitraryProposition :: Arbitrary a => Int -> Gen (Propositional a)
      sizedArbitraryProposition n
        | n <= 0 = fmap Proposition arbitrary
        | otherwise = oneof [ fmap Proposition arbitrary
                            , liftM2 (:&:) halfSizeSubFormula halfSizeSubFormula
                            , liftM2 (:|:) halfSizeSubFormula halfSizeSubFormula
                            , liftM2 (:->:) halfSizeSubFormula halfSizeSubFormula
                            , fmap Not (sizedArbitraryProposition (n - 1))
                            , return Verum
                            , return Falsum ]
        where
          halfSizeSubFormula = sizedArbitraryProposition (n `div` 2)
