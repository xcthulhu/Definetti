{-# LANGUAGE DeriveFunctor       #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections       #-}
module Logic.LinearProgramming where
import           Control.Monad (when)
import           Data.Monoid   ((<>))
import           Data.Ratio    (Rational, denominator)


data SumPlusConst a = [(a, String)] :+: a deriving (Eq, Show, Functor)

data LinearInequality a =
    SumPlusConst a :<:  SumPlusConst a
  | SumPlusConst a :<=: SumPlusConst a deriving (Eq, Show, Functor)

extractSumPlusConst :: SumPlusConst a -> [a]
extractSumPlusConst (prods :+: c) = c : fmap fst prods

extractLinearInequality :: LinearInequality a -> [a]
extractLinearInequality (x :<: y)  = extractSumPlusConst x ++ extractSumPlusConst y
extractLinearInequality (x :<=: y) = extractSumPlusConst x ++ extractSumPlusConst y

-- Infimum (ie, "lower bound") for `Int`
intInf :: Rational
intInf = fromIntegral (minBound :: Int)

-- Supremum (ie, "lower bound") for `Int`
intSup :: Rational
intSup = fromIntegral (maxBound :: Int)

-- Convert a linear programming problem using rational numbers to an integer programming problem
convertToIntegerProgramming :: [LinearInequality Rational]
                            -> Either String [LinearInequality Int]
convertToIntegerProgramming lp =
  let numbers = extractLinearInequality =<< lp
      multiplier = fromIntegral $ foldr lcm 1 (denominator <$> numbers)
      normalize r = do
        let r' = multiplier * r
        when (r' < intInf) $ Left (show r <> " is too small")
        when (intSup < r') $ Left (show r <> " is too large")
        pure $ truncate r'
      normalizeProd (a,x) = (,x) <$> normalize a
      toIntForm (summation :+: c) = do
        c'         <- normalize c
        summation' <- sequence (normalizeProd <$> summation)
        pure $ summation' :+: c'
      toIntProgramming (lhs :<: rhs)  = (:<:)  <$> toIntForm lhs <*> toIntForm rhs
      toIntProgramming (lhs :<=: rhs) = (:<=:) <$> toIntForm lhs <*> toIntForm rhs
  in sequence (toIntProgramming <$> lp)
