module Logic.Propositional
  ( module Tseitin
  , module Free
  ) where

import Logic.Propositional.Free as Free
  ( FreeModel(FreeModel)
  , FreeVars(Bound, Free)
  )
import Logic.Propositional.Internal.Tseitin as Tseitin
  ( Propositional((:&&:), (:->:), (:||:), Falsum, Not, Proposition,
              Verum)
  , conj
  , disj
  )
