module Logic.Semantics (module DPLL) where

import           Logic.Propositional.DPLL as DPLL (ConstrainedModelSearch (findConstrainedModel),
                                                   ModelSearch (findModel),
                                                   Semantics ((|=)))
