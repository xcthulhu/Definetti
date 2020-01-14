module Logic.Probability.Regression where

import Control.Applicative (Alternative((<|>), empty))
import Control.Exception (Exception)
import Control.Monad (MonadPlus, guard)
import Data.Bifunctor (first)
import Data.Ratio (Rational)
import Data.Typeable (Typeable)
import Data.List.NonEmpty (NonEmpty((:|)))

import Logic.Probability.Categorical
  ( Categorical
  , Probability((:*), (:+), Const, Pr)
  , pr
  )
import qualified Logic.Probability.Categorical as Categorical
import Logic.Probability.Inequality (ProbabilityInequality((:<)))
import Logic.Propositional (Propositional((:&&:)), conj)
import Logic.Propositional.Internal.DPLL (ConstrainedModelSearch)
import Logic.Semantics (ModelSearch(findModel))

data ProbabilityRegressionException p
  = EpsNotInOpenUnitInterval Rational
  | LawsNotSatisfiable [Propositional p]
  deriving (Show, Typeable)

instance (Show p, Typeable p) =>
         Exception (ProbabilityRegressionException p)

-- Model regression as a dynamical system
-- TODO: Use NonEmpty here
regressProbabilityOrbit ::
     (Ord p, MonadPlus m, Ord d, ConstrainedModelSearch d p m)
  => [Propositional p]
  -> [(Propositional p, Rational)]
  -> Rational
  -> m (Either (ProbabilityRegressionException p) (NonEmpty (Rational, Categorical d)))
regressProbabilityOrbit laws observations eps =
  (if eps <= 0 || 1 <= eps
     then pure . Left $ EpsNotInOpenUnitInterval eps
     else empty) <|>
  -- If eps is within bounds, proceed with calculation
  (do let lawsConj = conj laws
      initModel <- Categorical.dirac <$> findModel lawsConj
      let observations' = first (lawsConj :&&:) <$> observations
      Right . ((1, initModel) :|) <$> runRegression observations' eps initModel) <|>
  -- Since runRegression never actually fails, the only way we could be in this branch
  -- is if we failed to create an initial model by satisfying the laws provided
  (pure . Left $ LawsNotSatisfiable laws)

square :: Rational -> Rational
square r = r * r

findModelForImprovement ::
     (Ord p, Ord d, MonadPlus m, ConstrainedModelSearch d p m)
  => [(Propositional p, Rational)]
  -> Rational
  -> Categorical d
  -> m (Categorical d)
findModelForImprovement observations eps m =
  let f x = pr m (Pr x)
      currentError = sum [square (o - f x) | (x, o) <- observations]
        -- We must find some model where mixing it with our current model improves
        -- the error.  Error is measured with L2 distance.
        --
        -- It suffices to find a new model m' such that:
        --
        --  ∑ (oᵢ - ((1 - ε) * pr m ϕᵢ + ε * (pr m' ϕᵢ))) ** 2 < currentError
        --
        -- Furthermore, it is sufficient restrict search to 0-1 valued models.
        -- Under this assumption, we have
        --
        -- (1) (pr m' ϕᵢ)**2 = pr m' ϕᵢ
        --
        -- Using (1) the search problem may be transformed:
        --
        -- ∑ (oᵢ - ((1 - ε) * pr m ϕᵢ + ε * (pr m' ϕᵢ))) ** 2 < currentError
        --                         ≡
        -- ∑ ((oᵢ - (1 - ε) * pr m ϕᵢ) ** 2 +
        --      ε
        --    * (ε + 2 * (1 - ε) * pr m ϕᵢ - 2 * oᵢ)
        --    * (pr m' ϕᵢ))                                   < currentError
        --
        -- The latter is linear probability inequality satisfaction
        -- The decison procedure for these satisfaction problems
        -- always yield 0-1 valued models, hence our assumption in
        -- (1) is justified
      objectiveFunction =
        foldr
          (:+)
          (Const 0)
          [ Const newNorm2 :+ (coeff :* Pr x)
          | (x, o) <- observations
          , let prMProp' = (1 - eps) * f x
                newNorm2 = square (o - prMProp')
                coeff = eps * (eps + 2 * prMProp' - 2 * o)
          ]
   in if currentError == 0
        then empty
        else findModel (objectiveFunction :< Const currentError)

runRegressionStep ::
     (Ord p, Ord d, MonadPlus m, ConstrainedModelSearch d p m)
  => [(Propositional p, Rational)]
  -> Rational
  -> Categorical d
  -> m (Rational, Categorical d)
runRegressionStep observations eps m = do
  m' <- findModelForImprovement observations eps m
  let f x = pr m (Pr x)
      g x = pr m' (Pr x)
      denom = sum [square (g x - f x) | (x, _) <- observations]
  guard $ denom /= 0
  let alpha = sum [(g x - f x) * (o - f x) | (x, o) <- observations] / denom
  pure (alpha, Categorical.mix alpha m m')

runRegression ::
     (Ord p, Ord d, MonadPlus m, ConstrainedModelSearch d p m)
  => [(Propositional p, Rational)]
  -> Rational
  -> Categorical d
  -> m [(Rational, Categorical d)]
runRegression observations eps m =
  (do (alpha, improvedM) <- runRegressionStep observations eps m
      ((alpha, improvedM) :) <$> runRegression observations eps improvedM) <|>
  pure []
