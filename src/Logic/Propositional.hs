module Logic.Propositional (module Propositional, module DPLL) where

import           Logic.Propositional.DPLL    as DPLL (ConstraintProblem,
                                                      Literal (Neg, Pos))
import           Logic.Propositional.Tseitin as Propositional (Propositional ((:&&:), (:->:), (:||:), Falsum, Not, Proposition, Verum))
