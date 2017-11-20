module Logic.Formula.Data.MaxSatClause ( MaxSatClause(..) ) where
import           Data.Set
import           Logic.Formula.Data.Literal

-- | Weighted Clauses for Basic Weighted Max/Min Sat
-- A Clause is a list of literals
-- In Basic Weighted Max/Min Sat, clauses may either 'Hard' or 'Soft'
-- 'Hard' clauses are required to be satisfied
-- The goal of optimization is to maximize/minimal the number of 'Soft' clauses
data MaxSatClause a = Hard (Set(Literal a)) | Soft (Set(Literal a)) deriving (Ord, Show, Eq)
