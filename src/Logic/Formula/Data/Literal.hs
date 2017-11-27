module Logic.Formula.Data.Literal ( Literal(..), Definitional(..), Clause ) where
import qualified Data.Set as Set

-- | Definitional Atoms
-- Inspired by John Harrison's "Handbook of Practical Logic and Automated Reasoning", Section 2.8, pgs. 75-77
data Definitional a = Definition Int  -- ^ Represents a literal that defines a subterm
                    | Atom a          -- ^ Represents a literal for an atom in a formula
                    deriving (Ord, Show, Eq)

-- | Definitional Literals for Definitional Conjunctive Normal Form
data Literal a = Pos a | Neg a deriving (Ord, Show, Eq)

-- | Clauses are sets of literals
type Clause a = Set.Set (Literal a)
