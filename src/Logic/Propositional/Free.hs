{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeSynonymInstances  #-}

module Free where

import qualified Data.Set
import           Logic.Propositional.DPLL (ConjClause, Literal (..))
import           Logic.Semantics          (Semantics ((|=)))


-- Ultimate goal for data types: Free (Temporal (Free LinearProgram))
data Free p = Bound p | Free String

instance Semantics model (ConjClause a) => Semantics (Data.Set.Set String, model) (ConjClause (Free a)) where
  (|=) (freeVariablesSetToTrue, m) = all checkedToBeTrue
    where
      checkedToBeTrue (Neg l)         = not (checkedToBeTrue (Pos l))
      checkedToBeTrue (Pos (Bound p)) = m |= Data.Set.singleton (Pos p)
      checkedToBeTrue (Pos (Free v))  = v `Data.Set.member` freeVariablesSetToTrue
