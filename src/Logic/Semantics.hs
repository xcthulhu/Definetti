{-# LANGUAGE MultiParamTypeClasses #-}

module Logic.Semantics
  ( Semantics ((|=))
  , ModelSearch (findModel)
  ) where


-- | Truth-functional semantics
class Semantics model formula where
  infixr 6 |=
  (|=) :: model -> formula -> Bool

-- | ModelSearch
--
-- Model Search extends truth functional semantics
-- with a model search procedure that obeys the
-- the following law:
--
-- @
-- fmap (|= p) (findModel p) == fmap (const True) (findModel p)
-- @
--
class (Semantics model formula, Functor m) => ModelSearch m model formula where
  findModel :: formula -> m model
