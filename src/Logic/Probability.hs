module Logic.Probability
  ( module Categorical
  , module Inequalities
  ) where

import Logic.Probability.Categorical as Categorical
import Logic.Probability.Inequalities as Inequalities
  ( ProbabilityInequality((:<), (:<=), (:>), (:>=))
  )
