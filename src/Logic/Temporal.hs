module Logic.Temporal where

import           Logic.Propositional (Propositional)


data Temporal a = a `Until` a | Expr (Propositional a)
