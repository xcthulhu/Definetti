{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module Logic.Propositional.Free (FreeVars (Bound, Free), FreeModel (FreeModel)) where

import           Control.Applicative      (Alternative (empty))
import           Control.Monad            (guard)
import qualified Data.Set
import           Logic.Propositional.DPLL (ConstraintProblem,
                                           Literal (Neg, Pos))
import           Logic.Semantics          (ConstrainedModelSearch (findConstrainedModel),
                                           Semantics ((|=)))


data FreeVars v p =  Free v | Bound p deriving (Ord, Eq, Show)

instance Functor (FreeVars v) where
  fmap _ (Free v)  = Free v
  fmap f (Bound b) = Bound (f b)

data FreeModel v d = FreeModel (Data.Set.Set v) d

instance ( Ord a
         , Semantics d p
         ) => Semantics (FreeModel a d) (ConstraintProblem (FreeVars a p)) where
  (|=) (FreeModel freeVariablesSetToTrue m) = all checkedToBeTrue
    where
      checkedToBeTrue (Neg l)         = not (checkedToBeTrue (Pos l))
      checkedToBeTrue (Pos (Bound p)) = m |= p
      checkedToBeTrue (Pos (Free v))  = v `Data.Set.member` freeVariablesSetToTrue

instance ( Ord a
         , Ord p
         , Alternative f
         , ConstrainedModelSearch d p f
         ) => ConstrainedModelSearch (FreeModel a d) (FreeVars a p) f where
  findConstrainedModel clause =
    FreeModel <$> maybe empty pure maybeFreeVariablesSetToTrue
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
