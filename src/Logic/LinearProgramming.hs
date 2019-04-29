{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NamedFieldPuns        #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TupleSections         #-}

module Logic.LinearProgramming where

import           Prelude                hiding (sequence)

import           Control.Exception      (Exception, throwIO)
import           Control.Monad          (MonadPlus, forM, join, mzero, when,
                                         (<=<))
import           Control.Monad.IO.Class (MonadIO, liftIO)
import           Data.Foldable          (foldMap, toList)
import           Data.List              (isPrefixOf, nub)
import qualified Data.Map               as Map
import           Data.Maybe             (fromMaybe)
import           Data.Ratio             (Rational)
import           Data.Traversable       (sequence)
import           Data.Typeable          (Typeable)
import           Text.Printf            (printf)
import qualified Z3.Monad               as Z3

import           Logic.Propositional    (ConstrainedModelSearch (findConstrainedModel),
                                         ConstraintProblem, Literal (Neg, Pos))
import           Logic.Semantics        (Semantics ((|=)))

infix 7 :+:

data SumPlusConstant =
  [(Rational, String)] :+: Rational
  deriving (Ord, Eq, Show)

infix 6 :<:, :<=:

data LinearInequality
  = SumPlusConstant :<: SumPlusConstant
  | SumPlusConstant :<=: SumPlusConstant
  deriving (Ord, Eq, Show)

{- --------------- Linear Programming Solver --------------- -}
extractLPVarNames :: [LinearInequality] -> [String]
extractLPVarNames = nub . (extractLinearInequalityVars =<<)
  where
    extractSumVars (weightedVars :+: _) = snd <$> weightedVars
    extractLinearInequalityVars (x :<: y)  = foldMap extractSumVars [x, y]
    extractLinearInequalityVars (x :<=: y) = foldMap extractSumVars [x, y]

type LPVarMap = Map.Map String Z3.AST

type LPSolution = Map.Map String Rational

data IllegalVariableException = IllegalVariableException
  { illegalVariableName   :: String
  , illegalVariablePrefix :: String
  }

instance Show IllegalVariableException where
  show IllegalVariableException {illegalVariableName, illegalVariablePrefix} =
    printf
      "Illegal variable name: %s; variables cannot start with %s"
      (show illegalVariableName)
      (show illegalVariablePrefix)

instance Exception IllegalVariableException

illegalLPVariablePrefix :: String
illegalLPVariablePrefix = "@@@"

z3ExtractLPVarMap :: Z3.MonadZ3 z3 => [LinearInequality] -> z3 LPVarMap
z3ExtractLPVarMap lpProg =
  fmap Map.fromList . forM (extractLPVarNames lpProg) $ \varName -> do
    when (illegalLPVariablePrefix `isPrefixOf` varName) $
      (liftIO . throwIO)
        IllegalVariableException
          { illegalVariableName = varName
          , illegalVariablePrefix = illegalLPVariablePrefix
          }
    (varName, ) <$> Z3.mkFreshRealVar varName

data MissingVariableKeyException k v = MissingVariableKeyException
  { missingVariableKey :: k
  , variableMap        :: Map.Map k v
  }

instance Show k => Show (MissingVariableKeyException k v) where
  show MissingVariableKeyException {missingVariableKey, variableMap} =
    printf
      "Missing variable key: %s; possible variables in map: %s"
      (show missingVariableKey)
      (show $ Map.keys variableMap)

instance (Show k, Typeable k, Typeable v) =>
         Exception (MissingVariableKeyException k v)

lookupOrThrow :: MonadIO m => String -> LPVarMap -> m Z3.AST
lookupOrThrow varName varMap =
  case Map.lookup varName varMap of
    Just value -> pure value
    Nothing ->
      liftIO . throwIO $
      MissingVariableKeyException
        {missingVariableKey = varName, variableMap = varMap}

z3CoeffProd :: Z3.MonadZ3 z3 => LPVarMap -> Rational -> String -> z3 Z3.AST
z3CoeffProd varMap a v = do
  z3a <- Z3.mkRational a
  z3v <- lookupOrThrow v varMap
  Z3.mkMul [z3a, z3v]

lPSumPlusConst :: Z3.MonadZ3 z3 => LPVarMap -> SumPlusConstant -> z3 Z3.AST
lPSumPlusConst varMap (summands :+: c) = do
  z3c <- Z3.mkRational c
  z3prods <- forM summands (uncurry $ z3CoeffProd varMap)
  Z3.mkAdd $ z3c : z3prods

lPLinearInequality :: Z3.MonadZ3 z3 => LPVarMap -> LinearInequality -> z3 Z3.AST
lPLinearInequality varMap (x :<: y) = do
  z3x <- lPSumPlusConst varMap x
  z3y <- lPSumPlusConst varMap y
  z3x `Z3.mkLt` z3y
lPLinearInequality varMap (x :<=: y) = do
  z3x <- lPSumPlusConst varMap x
  z3y <- lPSumPlusConst varMap y
  z3x `Z3.mkLe` z3y

z3EvalLPVarMap ::
     Z3.MonadZ3 z3
  => Map.Map String Z3.AST
  -> Z3.Model
  -> z3 (Maybe (Map.Map String Rational))
z3EvalLPVarMap varMap model =
  fmap Map.fromList . sequence <$>
  forM
    (Map.toList varMap)
    (\(k, v) -> (fmap . fmap) (k, ) (Z3.evalReal model v))

z3SolveLP ::
     Z3.MonadZ3 z3 => [LinearInequality] -> z3 (Maybe (Map.Map String Rational))
z3SolveLP linearProg = do
  varMap <- z3ExtractLPVarMap linearProg
  Z3.assert =<< Z3.mkAnd =<< forM linearProg (lPLinearInequality varMap)
  fmap (join . snd) . Z3.withModel $ z3EvalLPVarMap varMap

-- | Solve a linear programming problem by finding a feasible solution
solveLP ::
     (MonadIO m, MonadPlus m)
  => [LinearInequality]
  -> m (Map.Map String Rational)
solveLP = maybe mzero pure <=< liftIO . Z3.evalZ3 . z3SolveLP

-- | Evaluates a 'SumPlusConstant' data structure
--   Variables not present in model default to value '0'
evalSumPlusConstant :: Map.Map String Rational -> SumPlusConstant -> Rational
evalSumPlusConstant varMap (summation :+: c) =
  sum
    [ coeff * fromMaybe 0 (Map.lookup variable varMap)
    | (coeff, variable) <- summation
    ] +
  c

instance Semantics (Map.Map String Rational) LinearInequality where
  m |= (lhs :<: rhs) = evalSumPlusConstant m lhs < evalSumPlusConstant m rhs
  m |= (lhs :<=: rhs) = evalSumPlusConstant m lhs <= evalSumPlusConstant m rhs

instance Semantics (Map.Map String Rational) [LinearInequality] where
  (|=) m = all (m |=)

instance Semantics (Map.Map String Rational) (ConstraintProblem LinearInequality) where
  m |= clauses = all (m |=) posClauses && all (not . (m |=)) negClauses
    where
      clauseList = toList clauses
      posClauses = [c | Pos c <- clauseList]
      negClauses = [c | Neg c <- clauseList]

instance (MonadIO m, MonadPlus m) =>
         ConstrainedModelSearch (Map.Map String Rational) LinearInequality m where
  findConstrainedModel = solveLP . fmap fromLit . toList
    where
      fromLit (Pos x)              = x
      fromLit (Neg (lhs :<: rhs))  = rhs :<=: lhs
      fromLit (Neg (lhs :<=: rhs)) = rhs :<: lhs
