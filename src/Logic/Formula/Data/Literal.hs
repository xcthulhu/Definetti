module Logic.Formula.Data.Literal ( Literal(..), Definitional(..) ) where

-- | Definitional Atoms
-- Inspired by John Harrison's "Handbook of Practical Logic and Automated Reasoning", Section 2.8, pgs. 75-77
data Definitional a = Definition Int  -- ^ Represents a literal that defines a subterm
                    | Atom a          -- ^ Represents a literal for an atom in a formula
                    deriving (Ord, Show, Eq)

-- | Definitional Literals for Definitional Conjunctive Normal Form
data Literal a = Pos a | Neg a deriving (Ord, Show, Eq)
