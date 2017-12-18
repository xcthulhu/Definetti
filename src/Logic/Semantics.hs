{-# LANGUAGE MultiParamTypeClasses #-}
module Logic.Semantics (Semantics (..), ModelSearch (..)) where

-- | Model theoretic semantics
class Semantics model formula where
  (|=) :: model -> formula -> Bool

-- | ModelSearch law:
--
-- @
-- all (|= p) (ModelSearch p)
-- @

class Semantics model formula => ModelSearch model formula where
  findModel :: formula -> Maybe model
