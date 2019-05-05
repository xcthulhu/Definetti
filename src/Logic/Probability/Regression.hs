module Logic.Probability.Regression where

-- import Control.Arrow (second)
-- import Control.Monad (MonadPlus(mplus, mzero))
-- import Data.Foldable (fold)
-- import Data.List (sortOn)

import Logic.Propositional (Propositional)
-- import Logic.Propositional.Internal.DPLL (CNF)
-- import Logic.Propositional.Internal.Tseitin (tseitinTransform)
-- import Logic.Semantics (ConstrainedModelSearch, ModelSearch(findModel))

data ProbabilityRegressionProblem p = ProbabilityRegressionProblem
  { laws :: [Propositional p]
  , observations :: [(Propositional p, Rational)]
  }
