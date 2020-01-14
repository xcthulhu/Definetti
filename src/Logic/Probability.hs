module Logic.Probability
  ( module Categorical
  , module Inequality
  ) where

import Logic.Probability.Categorical as Categorical
import Logic.Probability.Inequality as Inequality
  ( ProbabilityInequality((:<), (:<=), (:>), (:>=))
  )
