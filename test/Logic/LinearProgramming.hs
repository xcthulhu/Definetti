{-# LANGUAGE DeriveFunctor         #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TupleSections         #-}
module Logic.LinearProgramming where
import           Control.Arrow          (first)
import           Control.Exception.Safe (Exception, Typeable, throwIO)
import           Control.Monad          (MonadPlus, forM, join, mzero, (<=<))
import           Control.Monad.IO.Class (MonadIO, liftIO)
import           Data.Foldable          (foldMap, toList)
import           Data.List              (nub)
import qualified Data.Map               as Map
import           Data.Ratio             (Rational, denominator)
import           Logic.Propositional    (ConstrainedModelSearch (findConstrainedModel),
                                         Literal (Neg, Pos))
import qualified Z3.Monad               as Z3


data SumPlusConstant a = [(a, String)] :+: a deriving (Ord, Eq, Show, Functor)

data LinearInequality a =
    SumPlusConstant a :<:  SumPlusConstant a
  | SumPlusConstant a :<=: SumPlusConstant a deriving (Ord, Eq, Show, Functor)

extractSumPlusConstant :: SumPlusConstant a -> [a]
extractSumPlusConstant (prods :+: c) = c : fmap fst prods

extractLinearInequalityNumbers :: LinearInequality a -> [a]
extractLinearInequalityNumbers (x :<: y) = foldMap extractSumPlusConstant [x, y]
extractLinearInequalityNumbers (x :<=: y) = foldMap extractSumPlusConstant [x, y]

-- | Convert a linear programming problem with rational numbers to an integer programming problem
--   Keeps track of the normalization constant so a solution may be converted back
convertToIntegerProgramming :: [LinearInequality Rational] -> (Integer, [LinearInequality Integer])
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

z3ExtractIPVarMap :: Z3.MonadZ3 z3
                  => [LinearInequality Integer]
                  -> z3 IPVarMap
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
lookupOrThrow v m = maybe (liftIO . throwIO $ MissingVariableKeyException v m)
                           pure
                           (Map.lookup v m)

z3CoeffProd :: Z3.MonadZ3 z3
            => IPVarMap
            -> Integer
            -> String
            -> z3 Z3.AST
z3CoeffProd varMap a v = do
  z3a <- Z3.mkInteger a
  z3v <- lookupOrThrow v varMap
  Z3.mkMul [z3a, z3v]

z3IPSumPlusConst :: Z3.MonadZ3 z3
                 => IPVarMap
                 -> SumPlusConstant Integer
                 -> z3 Z3.AST
z3IPSumPlusConst varMap (summands :+: c) = do
  z3c     <- Z3.mkInteger c
  z3prods <- forM summands (uncurry $ z3CoeffProd varMap)
  Z3.mkAdd $ z3c : z3prods

z3IPLinearInequality :: Z3.MonadZ3 z3
                     => IPVarMap
                     -> LinearInequality Integer
                     -> z3 Z3.AST
z3IPLinearInequality varMap (x :<: y) = do
  z3x <- z3IPSumPlusConst varMap x
  z3y <- z3IPSumPlusConst varMap y
  z3x `Z3.mkLt` z3y
z3IPLinearInequality varMap (x :<=: y) = do
  z3x <- z3IPSumPlusConst varMap x
  z3y <- z3IPSumPlusConst varMap y
  z3x `Z3.mkLe` z3y

z3SolveIP :: Z3.MonadZ3 z3
          => [LinearInequality Integer]
          -> z3 (Maybe (Map.Map String Integer))
z3SolveIP intProg = do
  varMap <- z3ExtractIPVarMap intProg
  Z3.assert =<< Z3.mkAnd =<< forM intProg (z3IPLinearInequality varMap)
  fmap (join . snd) . Z3.withModel $ \m -> do
    pairs <- forM (Map.toList varMap) $ \ (k,v) ->
      (fmap . fmap) (k,) (Z3.evalInt m v)
    pure . fmap Map.fromList . sequence $ pairs

liftMaybe :: MonadPlus m => Maybe a -> m a
liftMaybe = maybe mzero pure

-- | Solve an Integer programming problem
solveIP :: (MonadIO m, MonadPlus m)
        => [LinearInequality Integer]
        -> m (Map.Map String Integer)
solveIP =   liftMaybe
        <=< liftIO
        .   Z3.evalZ3
        .   z3SolveIP

-- | Find an exact solution to a linear programming problem
--   (with rational coefficients) by converting it into an
--   integer programming problem and converting the answer back
--   into rational numbers
solveLP :: (MonadIO f, MonadPlus f)
        => [LinearInequality Rational]
        -> f (Map.Map String Rational)
solveLP lp =
  let (normalizer, ip) = convertToIntegerProgramming lp
  in Map.map (\v -> fromIntegral v / fromIntegral normalizer) <$> solveIP ip

instance (MonadIO m, MonadPlus m)
         => ConstrainedModelSearch (Map.Map String Rational)
                                   (LinearInequality Rational)
                                   m
  where
    findConstrainedModel = solveLP . fmap fromLit . toList
      where fromLit (Pos x)              = x
            fromLit (Neg (lhs :<: rhs))  = rhs :<=: lhs
            fromLit (Neg (lhs :<=: rhs)) = rhs :<: lhs
