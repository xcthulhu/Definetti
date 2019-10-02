{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RecordWildCards #-}

module Logic.Propositional.Free
  ( FreeVars(Bound, Free)
  , FreeModel(FreeModel)
  ) where

import Control.Applicative (Alternative(empty))
import Control.Monad (guard)
import qualified Data.Set
import Logic.Propositional.Internal.DPLL (Literal(Neg, Pos))
import Logic.Semantics
  ( ConstrainedModelSearch(findConstrainedModel)
  , Semantics((|=))
  )

data FreeVars v p
  = Free v
  | Bound p
  deriving (Ord, Eq, Show)

instance Functor (FreeVars v) where
  fmap _ (Free v) = Free v
  fmap f (Bound b) = Bound (f b)

data FreeModel v d = FreeModel
  { freeVariablesSetToTrue :: Data.Set.Set v
  , model :: d
  } deriving (Eq, Show, Ord)

instance (Ord v, Semantics d p) =>
         Semantics (FreeModel v d) (FreeVars v p) where
  FreeModel {..} |= (Bound p) = model |= p
  FreeModel {..} |= (Free v) = v `Data.Set.member` freeVariablesSetToTrue

instance (Ord v, Ord p, Alternative f, ConstrainedModelSearch d p f) =>
         ConstrainedModelSearch (FreeModel v d) (FreeVars v p) f where
  findConstrainedModel clause =
    FreeModel <$> maybe empty pure maybeFreeVariablesSetToTrue <*>
    findConstrainedModel boundLiterals
    where
      maybeFreeVariablesSetToTrue =
        fst <$> Data.Set.foldr tryAddFreeLit initFreeLits clause
      initFreeLits = pure (Data.Set.empty, Data.Set.empty)
      tryAddFreeLit _ Nothing = Nothing
      tryAddFreeLit (Pos (Free p)) maybeVars = do
        (posVars, negVars) <- maybeVars
        guard . not $ p `Data.Set.member` negVars
        pure (Data.Set.insert p posVars, negVars)
      tryAddFreeLit (Neg (Free p)) maybeVars = do
        (posVars, negVars) <- maybeVars
        guard . not $ p `Data.Set.member` posVars
        pure (posVars, Data.Set.insert p negVars)
      tryAddFreeLit _ maybeFreeVars = maybeFreeVars
      boundLiterals = Data.Set.foldr addBoundLit Data.Set.empty clause
      addBoundLit (Neg (Bound p)) ls = Data.Set.insert (Neg p) ls
      addBoundLit (Pos (Bound p)) ls = Data.Set.insert (Pos p) ls
      addBoundLit _ ls = ls
