module Logic.Formula.Data.MaxSatClause ( MaxSatClause(..) ) where
import           Data.Set
import           Logic.Formula.Data.Literal

-- | Clauses for Max/Min Sat
-- A clause has a top variable that represents
-- other clauses serve as definitions relevant to the top literal
data MaxSatClause a = MaxSatClause { topValue :: a
                                   , definitionalClauses :: Set (Literal a)
                                   } deriving (Ord, Show, Eq)
