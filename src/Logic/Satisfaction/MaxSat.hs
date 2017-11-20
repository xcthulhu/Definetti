module Logic.Satisfaction.MaxSat() where
import           Control.Monad              (MonadPlus, guard, join, mplus,
                                             msum, mzero)
import           Data.Maybe                 (listToMaybe)
import           Data.Set                   (Set, (\\))
import qualified Data.Set                   as Set
import           Logic.Formula.Data.Literal
import           Logic.Formula.Data.MaxSatClause

neg :: Literal p -> Literal p
neg (Pos p) = Neg p
neg (Neg p) = Pos p

-- We model DPLL like a sequent calculus
-- LHS: a set of assumptions / partial model (set of literals)
-- RHS: a set of goals
data Sequent p = (Set (Literal p)) :|-: Set (Set (Literal p)) deriving Show

{- --------------------------- Goal Reduction Rules -------------------------- -}
{- "Unit Propogation" takes literal x and A :|-: B to A,x :|-: B',
 - where B' has no clauses with x,
 - and all instances of -x are deleted -}
unitP :: Ord p => Literal p -> Sequent p -> Sequent p
unitP x (assms :|-:  clauses) = (assms' :|-:  clauses')
  where
    assms' = Set.insert x assms
    clauses_ = Set.filter (not . (x `Set.member`)) clauses
    clauses' = Set.map (Set.filter (/= neg x)) clauses_

{- Find literals that only occur positively or negatively
 - and perform unit propogation on these -}
pureRule sequent@(_ :|-:  clauses) =
  let
    sign (Pos _) = True
    sign (Neg _) = False
    -- Partition the positive and negative formulae
    (positive,negative) = Set.partition sign (Set.unions . Set.toList $ clauses)
    -- Compute the literals that are purely positive/negative
    purePositive = positive \\ (Set.map neg negative)
    pureNegative = negative \\ (Set.map neg positive)
    pure = purePositive `Set.union` pureNegative
    -- Unit Propagate the pure literals
    sequent' = foldr unitP sequent pure
  in if (not $ Set.null pure) then return sequent'
     else mzero

{- Add any singleton clauses to the assumptions
 - and simplify the clauses -}
oneRule sequent@(_ :|-:  clauses) =
   do
   -- Extract literals that occur alone and choose one
   let singletons = concatMap Set.toList . filter isSingle $ Set.toList clauses
   case singletons of
     x:_ -> return $ unitP x sequent  -- Return the new simplified problem
     [] -> mzero
   where
     isSingle c = case (Set.toList c) of { [a] -> True ; _ -> False }

{- ------------------------------ DPLL Algorithm ----------------------------- -}
dpll goalClauses = dpll' $ Set.empty :|-: goalClauses
  where
     dpll' sequent@(assms :|-: clauses) = do
       -- Fail early if falsum is a subgoal
       guard $ not (Set.empty `Set.member` clauses)
       case concatMap Set.toList $ Set.toList clauses of
         -- Return the assumptions if there are no subgoals left
         []  -> return assms
         -- Otherwise try various tactics for resolving goals
         x:_ -> dpll' =<< msum [ pureRule sequent
                                , oneRule sequent
                                , return $ unitP x sequent
                                , return $ unitP (neg x) sequent ]

