{-# LANGUAGE DeriveFunctor         #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NamedFieldPuns        #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TupleSections         #-}

module Logic.LinearProgramming where

import           Prelude                hiding (sequence)

import           Control.Arrow          (first)
import           Control.Exception.Safe (Exception, Typeable, throwIO)
import           Control.Monad          (MonadPlus, forM, join, mzero, when,
                                         (<=<))
import           Control.Monad.IO.Class (MonadIO, liftIO)
import           Data.Foldable          (foldMap, toList)
import           Data.List              (isPrefixOf, nub)
import qualified Data.Map               as Map
import           Data.Maybe             (fromMaybe)
import           Data.Ratio             (Rational, denominator)
import           Data.Traversable       (sequence)
import           Text.Printf            (printf)
import qualified Z3.Monad               as Z3

import           Logic.Propositional    (ConstrainedModelSearch (findConstrainedModel),
                                         ConstraintProblem, Literal (Neg, Pos))
import           Logic.Semantics        (Semantics ((|=)))


infix 7 :+:
data SumPlusConstant a = [(a, String)] :+: a deriving (Ord, Eq, Show, Functor)

infix 6 :<:, :<=:
data LinearInequality a =
    SumPlusConstant a :<:  SumPlusConstant a
  | SumPlusConstant a :<=: SumPlusConstant a deriving (Ord, Eq, Show, Functor)

extractSumPlusConstant :: SumPlusConstant a -> [a]
extractSumPlusConstant (prods :+: c) = c : fmap fst prods

extractLinearInequalityNumbers :: LinearInequality a -> [a]
extractLinearInequalityNumbers (x :<: y) =
  foldMap extractSumPlusConstant [x, y]
extractLinearInequalityNumbers (x :<=: y) =
  foldMap extractSumPlusConstant [x, y]

-- | Convert a linear programming problem with rational numbers to an integer programming problem
--   Keeps track of the normalization constant so a solution may be converted back
convertToIntegerProgramming
  :: [LinearInequality Rational] -> (Integer, [LinearInequality Integer])
convertToIntegerProgramming lp =
  let numbers    = extractLinearInequalityNumbers =<< lp
      -- normalize by multiplying through with LCM of denominators
      normalizer = foldr lcm 1 (denominator <$> numbers)
      normalize  = floor . (* fromInteger normalizer)
      toIntSumPlusConst (summation :+: c) =
        (first normalize <$> summation) :+: normalize c
      toIntProgramming (lhs :<: rhs) =
        toIntSumPlusConst lhs :<: toIntSumPlusConst rhs
      toIntProgramming (lhs :<=: rhs) =
        toIntSumPlusConst lhs :<=: toIntSumPlusConst rhs
  in  (normalizer, toIntProgramming <$> lp)

{- --------------- Linear Programming Solver --------------- -}

extractIPVarNames :: [LinearInequality Integer] -> [String]
extractIPVarNames = nub . (extractLinearInequalityVars =<<)
 where
  extractSumVars (weightedVars :+: _) = snd <$> weightedVars
  extractLinearInequalityVars (x :<:  y) = foldMap extractSumVars [x, y]
  extractLinearInequalityVars (x :<=: y) = foldMap extractSumVars [x, y]

type IPVarMap = Map.Map String Z3.AST
type IPSolution = Map.Map String Integer

data IllegalVariableException =
  IllegalVariableException { illegalVariableName   :: String
                           , illegalVariablePrefix :: String
                           }

instance Show IllegalVariableException where
  show (IllegalVariableException {illegalVariableName, illegalVariablePrefix}) =
    printf "Illegal variable name: %s; variables cannot start with %s"
           (show illegalVariableName)
           (show illegalVariablePrefix)

instance Exception IllegalVariableException

illegalIPVariablePrefix :: String
illegalIPVariablePrefix = "@@@"

z3ExtractIPVarMap :: Z3.MonadZ3 z3 => [LinearInequality Integer] -> z3 IPVarMap
z3ExtractIPVarMap intProg =
  fmap Map.fromList . forM (extractIPVarNames intProg) $ \varName -> do
    when (illegalIPVariablePrefix `isPrefixOf` varName) $ (liftIO . throwIO)
      IllegalVariableException
        { illegalVariableName   = varName
        , illegalVariablePrefix = illegalIPVariablePrefix
        }
    (varName, ) <$> Z3.mkFreshIntVar varName

data MissingVariableKeyException k v =
  MissingVariableKeyException { missingVariableKey :: k
                              , variableMap        :: Map.Map k v
                              }

instance Show k => Show (MissingVariableKeyException k v) where
  show MissingVariableKeyException {missingVariableKey, variableMap} =
    printf "Missing variable key: %s; possible variables in map: %s"
          (show missingVariableKey)
          (show $ Map.keys variableMap)

instance (Show k, Typeable k, Typeable v) => Exception (MissingVariableKeyException k v)

lookupOrThrow :: MonadIO m => String -> IPVarMap -> m Z3.AST
lookupOrThrow varName varMap = case Map.lookup varName varMap of
  Just value -> pure value
  Nothing    -> liftIO . throwIO $ MissingVariableKeyException
    { missingVariableKey = varName
    , variableMap        = varMap
    }

z3CoeffProd :: Z3.MonadZ3 z3 => IPVarMap -> Integer -> String -> z3 Z3.AST
z3CoeffProd varMap a v = do
  z3a <- Z3.mkInteger a
  z3v <- lookupOrThrow v varMap
  Z3.mkMul [z3a, z3v]

z3IPSumPlusConst
  :: Z3.MonadZ3 z3 => IPVarMap -> SumPlusConstant Integer -> z3 Z3.AST
z3IPSumPlusConst varMap (summands :+: c) = do
  z3c     <- Z3.mkInteger c
  z3prods <- forM summands (uncurry $ z3CoeffProd varMap)
  Z3.mkAdd $ z3c : z3prods

z3IPLinearInequality
  :: Z3.MonadZ3 z3 => IPVarMap -> LinearInequality Integer -> z3 Z3.AST
z3IPLinearInequality varMap (x :<: y) = do
  z3x <- z3IPSumPlusConst varMap x
  z3y <- z3IPSumPlusConst varMap y
  z3x `Z3.mkLt` z3y
z3IPLinearInequality varMap (x :<=: y) = do
  z3x <- z3IPSumPlusConst varMap x
  z3y <- z3IPSumPlusConst varMap y
  z3x `Z3.mkLe` z3y

z3EvalIPVarMap
  :: Z3.MonadZ3 z3
  => Map.Map String Z3.AST
  -> Z3.Model
  -> z3 (Maybe (Map.Map String Integer))
z3EvalIPVarMap varMap model = fmap Map.fromList . sequence <$> forM
  (Map.toList varMap)
  (\(k, v) -> (fmap . fmap) (k, ) (Z3.evalInt model v))

z3SolveIP
  :: Z3.MonadZ3 z3
  => [LinearInequality Integer]
  -> z3 (Maybe (Map.Map String Integer))
z3SolveIP intProg = do
  varMap <- z3ExtractIPVarMap intProg
  Z3.assert =<< Z3.mkAnd =<< forM intProg (z3IPLinearInequality varMap)
  fmap (join . snd) . Z3.withModel $ z3EvalIPVarMap varMap

fmapaybe :: MonadPlus m => Maybe a -> m a
fmapaybe = maybe mzero pure

-- | Solve an Integer programming problem
solveIP
  :: (MonadIO m, MonadPlus m)
  => [LinearInequality Integer]
  -> m (Map.Map String Integer)
solveIP = fmapaybe <=< liftIO . Z3.evalZ3 . z3SolveIP

-- | Evaluates a `SumPlusConstant n` data structure
--   Variables no present in model default to value @0@
evalSumPlusConstant :: Num n => Map.Map String n -> SumPlusConstant n -> n
evalSumPlusConstant m (summation :+: c) =
  sum
      [ coeff * fromMaybe 0 (Map.lookup variable m)
      | (coeff, variable) <- summation
      ]
    + c

instance (Ord n, Num n) => Semantics (Map.Map String n) (LinearInequality n) where
  m |= (lhs :<: rhs) = evalSumPlusConstant m lhs < evalSumPlusConstant m rhs
  m |= (lhs :<=: rhs) = evalSumPlusConstant m lhs <= evalSumPlusConstant m rhs

instance (Ord n, Num n) => Semantics (Map.Map String n) [LinearInequality n] where
  (|=) m = all (m |=)

instance (Ord n, Num n) => Semantics (Map.Map String n) (ConstraintProblem (LinearInequality n)) where
  m |= clauses = all (m |=) posClauses && all (not . (m |=)) negClauses
    where
      clauseList = toList clauses
      posClauses = [c | Pos c <- clauseList]
      negClauses = [c | Neg c <- clauseList]

-- | Find an exact solution to a linear programming problem
--   (with rational coefficients) by converting it into an
--   integer programming problem and converting the answer back
--   into rational numbers
solveLP
  :: (MonadIO f, MonadPlus f)
  => [LinearInequality Rational]
  -> f (Map.Map String Rational)
solveLP lp =
  let (normalizer, ip) = convertToIntegerProgramming lp
  in  Map.map (\v -> fromIntegral v / fromIntegral normalizer) <$> solveIP ip

instance (MonadIO m, MonadPlus m)
         => ConstrainedModelSearch (Map.Map String Rational)
                                   (LinearInequality Rational)
                                   m
  where
    findConstrainedModel = solveLP . fmap fromLit . toList
      where fromLit (Pos x)              = x
            fromLit (Neg (lhs :<: rhs))  = rhs :<=: lhs
            fromLit (Neg (lhs :<=: rhs)) = rhs :<: lhs
