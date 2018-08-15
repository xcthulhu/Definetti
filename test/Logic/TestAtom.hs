{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# OPTIONS_GHC -fno-warn-orphans  #-}

module Logic.TestAtom (Atom, AtomModel, bound)
where

import           Control.Applicative (Alternative, empty, pure)
import           Control.Monad       (liftM2)
import qualified Data.Set            (Set, filter, map, member)
import           Test.QuickCheck     (Arbitrary (arbitrary), Gen, oneof, sized)

import           Logic.Propositional (FreeModel, FreeVars (Bound, Free),
                                      Literal (Neg, Pos),
                                      Propositional ((:&&:), (:->:), (:||:), Falsum, Not, Proposition, Verum))
import           Logic.Semantics     (ConstrainedModelSearch (findConstrainedModel),
                                      Semantics ((|=)))


newtype Urelement a = Urelement a deriving (Ord, Eq, Show)

instance Arbitrary p => Arbitrary (Urelement p) where
  arbitrary = Urelement <$> arbitrary

instance (Arbitrary v, Arbitrary p) => Arbitrary (FreeVars v p) where
  arbitrary = oneof [Bound <$> arbitrary, Free <$> arbitrary]

type Atom p = FreeVars Char (Urelement p)

bound :: p -> Atom p
bound = Bound . Urelement

type AtomModel p = FreeModel Char (Data.Set.Set (Urelement p))

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

instance Ord p => Semantics (Data.Set.Set (Urelement p)) (Urelement p) where
  (|=) = flip Data.Set.member

-- | ModelSearch for conjunctions of urelements
-- If two of the variables in the conjunction contradict, fail (modeled with Control.Applicative.empty)
-- Otherwise return the set of positive variables
instance (Ord p, Alternative f) => ConstrainedModelSearch (Data.Set.Set (Urelement p))
                                                          (Urelement p)
                                                          f
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
