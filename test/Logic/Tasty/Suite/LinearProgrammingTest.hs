{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TupleSections         #-}
{-# OPTIONS_GHC -fno-warn-orphans  #-}

module Logic.Tasty.Suite.LinearProgrammingTest
--  ( linearProgrammingTests )
where

import           Prelude                   hiding (sequence)

import           Control.Arrow             (first)
import           Control.Exception.Safe    (Exception, Typeable, throwIO)
import           Control.Monad             (MonadPlus, forM, join, mzero, (<=<))
import           Control.Monad.IO.Class    (MonadIO, liftIO)
import           Control.Monad.Trans.Maybe (runMaybeT)
import           Data.Foldable             (foldMap)
import           Data.List                 (nub)
import qualified Data.Map                  as Map
import           Data.Maybe                (catMaybes)
import           Data.Ratio                (Rational, denominator)
import qualified Data.Set                  as Set
import           Data.Traversable          (sequence)
import           Logic.LinearProgramming   (LinearInequality ((:<:), (:<=:)),
                                            SumPlusConstant ((:+:)))
import           Prelude                   hiding (until)
import           Z3.Monad
import qualified Z3.Monad                  as Z3


import           Test.Tasty                (TestTree, testGroup)
import           Test.Tasty.HUnit          (testCase, (@?=))

import           Logic.Propositional       (ConstrainedModelSearch (findConstrainedModel),
                                            Literal)



findConstrainedModel'
  :: Set.Set (Literal (LinearInequality Rational)) -> IO (Maybe (Map.Map String Rational))
findConstrainedModel' = runMaybeT . findConstrainedModel

basicLinearProgrammingTests :: TestTree
basicLinearProgrammingTests = testGroup
  "Basic Tests"
  [ testCase "1/2 X <= X" $ do
      -- let lp = Set.fromList [Pos $ [(1 % 2, "X")] :+: 0 :<=: [(1 :: Rational, "X")] :+: 0]
      model <- runMaybeT fourQueens
      model @?= Nothing
  ]

linearProgrammingTests :: TestTree
linearProgrammingTests =
  testGroup "Linear Programming Tests" [basicLinearProgrammingTests]

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

z3ExtractIPVarMap :: Z3.MonadZ3 z3 => [LinearInequality Integer] -> z3 IPVarMap
z3ExtractIPVarMap intProg =
  Map.fromList <$> forM (extractIPVarNames intProg) mkFreshIntVarPair
  where mkFreshIntVarPair v = (v, ) <$> Z3.mkFreshIntVar v

data MissingVariableKeyException k v = MissingVariableKeyException k (Map.Map k v)

instance Show k => Show (MissingVariableKeyException k v) where
  show (MissingVariableKeyException missingVar varMap) = unwords
    [
      "Missing variable key:"
    , show missingVar
    , "possible variable values in IPVarMap:"
    , show $ Map.keys varMap
    ]

instance (Show k, Typeable k, Typeable v) => Exception (MissingVariableKeyException k v)

lookupOrThrow :: MonadIO m => String -> IPVarMap -> m Z3.AST
lookupOrThrow v m = maybe
  (liftIO . throwIO $ MissingVariableKeyException v m)
  pure
  (Map.lookup v m)

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

z3SolveIP
  :: Z3.MonadZ3 z3
  => [LinearInequality Integer]
  -> z3 (Maybe (Map.Map String Integer))
z3SolveIP intProg = do
  varMap <- z3ExtractIPVarMap intProg
  Z3.assert =<< Z3.mkAnd =<< forM intProg (z3IPLinearInequality varMap)
  fmap (join . snd) . Z3.withModel $ \m -> do
    pairs <- forM (Map.toList varMap)
      $ \(k, v) -> (fmap . fmap) (k, ) (Z3.evalInt m v)
    pure . fmap Map.fromList . sequence $ pairs

liftMaybe :: MonadPlus m => Maybe a -> m a
liftMaybe = maybe mzero pure

-- | Solve an Integer programming problem
solveIP
  :: (MonadIO m, MonadPlus m)
  => [LinearInequality Integer]
  -> m (Map.Map String Integer)
solveIP = liftMaybe <=< liftIO . Z3.evalZ3 . z3SolveIP

fourQueens
  :: (MonadIO m, MonadPlus m)
  => m [Integer]
fourQueens = liftMaybe <=< liftIO . evalZ3 $ do
  q1 <- mkFreshIntVar "q1"
  q2 <- mkFreshIntVar "q2"
  q3 <- mkFreshIntVar "q3"
  q4 <- mkFreshIntVar "q4"
  _1 <- mkInteger 1
  _4 <- mkInteger 4
  -- the ith-queen is in the ith-row.
  -- qi is the column of the ith-queen
  assert =<< mkAnd =<< sequence
    [ mkLe _1 q1, mkLe q1 _4  -- 1 <= q1 <= 4
    , mkLe _1 q2, mkLe q2 _4
    , mkLe _1 q3, mkLe q3 _4
    , mkLe _1 q4, mkLe q4 _4
    ]
  -- different columns
  assert =<< mkDistinct [q1,q2,q3,q4]
  -- avoid diagonal attacks
  assert =<< mkNot =<< mkOr =<< sequence
    [ diagonal 1 q1 q2  -- diagonal line of attack between q1 and q2
    , diagonal 2 q1 q3
    , diagonal 3 q1 q4
    , diagonal 1 q2 q3
    , diagonal 2 q2 q4
    , diagonal 1 q3 q4
    ]
  -- check and get solution
  fmap snd $ withModel $ \m ->
    catMaybes <$> mapM (evalInt m) [q1,q2,q3,q4]
  where mkAbs x = do
          _0 <- mkInteger 0
          join $ mkIte <$> mkLe _0 x <*> pure x <*> mkUnaryMinus x
        diagonal d c c' =
          join $ mkEq <$> (mkAbs =<< mkSub [c',c]) <*> (mkInteger d)

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
