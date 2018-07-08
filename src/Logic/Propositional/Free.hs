{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module Logic.Propositional.Free where

import           Control.Applicative (Alternative (empty))
import           Control.Monad       (guard)
import qualified Data.Set
import           Logic.Propositional (ConstraintProblem, Literal (Neg, Pos))
import           Logic.Semantics     (ConstrainedModelSearch (findConstrainedModel),
                                      Semantics ((|=)))


-- Ultimate goal for data types: FreeVars (Temporal (FreeVars LinearProgram))
data FreeVars p = Bound p | Free String

data FreeModel d = FreeModel (Data.Set.Set String) d

instance Semantics d a => Semantics (FreeModel d) (ConstraintProblem (FreeVars a)) where
  (|=) (FreeModel freeVariablesSetToTrue m) = all checkedToBeTrue
    where
      checkedToBeTrue (Neg l)         = not (checkedToBeTrue (Pos l))
      checkedToBeTrue (Pos (Bound p)) = m |= p
      checkedToBeTrue (Pos (Free v))  = v `Data.Set.member` freeVariablesSetToTrue

instance (Ord p, Alternative f, ConstrainedModelSearch f d p) => ConstrainedModelSearch f (FreeModel d) (FreeVars p) where
  findConstrainedModel clause = FreeModel <$> maybe empty pure maybeFreeVariablesSetToTrue
                                          <*> findConstrainedModel boundLiterals
    where
      maybeFreeVariablesSetToTrue =
        fst <$> Data.Set.foldr tryAddFreeLit initFreeLits clause

      initFreeLits = pure (Data.Set.empty, Data.Set.empty)

      tryAddFreeLit _              Nothing   = Nothing
      tryAddFreeLit (Pos (Free p)) maybeVars = do
        (posVars, negVars) <- maybeVars
        guard . not $ p `Data.Set.member` negVars
        pure (Data.Set.insert p posVars, negVars)
      tryAddFreeLit (Neg (Free p)) maybeVars = do
        (posVars, negVars) <- maybeVars
        guard . not $ p `Data.Set.member` posVars
        pure (posVars, Data.Set.insert p negVars)
      tryAddFreeLit _              maybeFreeVars = maybeFreeVars

      boundLiterals =
        Data.Set.foldr addBoundLit Data.Set.empty clause

      addBoundLit (Neg (Bound p)) ls = Data.Set.insert (Neg p) ls
      addBoundLit (Pos (Bound p)) ls = Data.Set.insert (Pos p) ls
      addBoundLit _               ls = ls
