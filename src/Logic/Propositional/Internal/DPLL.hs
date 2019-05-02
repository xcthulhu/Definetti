{-# LANGUAGE DeriveFunctor         #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MonoLocalBinds        #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module Logic.Propositional.Internal.DPLL
  ( Literal(Pos, Neg)
  , ConstraintProblem
  , HornClause
  , CNF
  , ModelSearch(findModel)
  , ConstrainedModelSearch(findConstrainedModel)
  , Semantics((|=))
  )
where

import           Control.Applicative (Alternative, empty, pure)
import           Control.Monad       (MonadPlus, guard, msum)
import qualified Data.Foldable       (concatMap, fold)
import           Data.Monoid         (mempty, (<>))
import           Data.Set            ((\\))
import qualified Data.Set            (Set, filter, intersection, map, member,
                                      null, partition, singleton, size, toList)


{- --------------------------------- Types -------------------------------- -}

-- | Definitional Literals for Definitional Conjunctive Normal Form
data Literal a = Pos a | Neg a deriving (Ord, Show, Eq, Functor)

-- | Clauses are sets of literals
type Clause a = Data.Set.Set (Literal a)

-- | Constraint problems are conjunction of literals
type ConstraintProblem a = Clause a

-- | Horn clauses are disjunctions of literals
type HornClause a = Clause a

-- | Conjunctive Normal Form
type CNF a = Data.Set.Set (HornClause a)


{- ------------------------------ Type Classes ----------------------------- -}

-- | Truth-functional semantics
class Semantics d p where
  infixr 6 |=
  (|=) :: d -> p -> Bool

-- | ModelSearch
--
-- Model Search interacts with truth functional semantics
-- by implementing a model search procedure that obeys
-- the following law:
--
-- @
-- fmap (|= p) (findModel p) == fmap (const True) (findModel p)
-- @
--
class ModelSearch d p f where
  findModel :: p -> f d

-- | ConstraintProblems are model searches over conjunctions of propositions
class ConstrainedModelSearch d l f where
  findConstrainedModel :: ConstraintProblem l -> f d


{- ------ Davis–Putnam–Logemann–Loveland Procedure for Model Search ------ -}

-- | Flip the sign of a literal
neg :: Literal p -> Literal p
neg (Pos p) = Neg p
neg (Neg p) = Pos p

-- | State for DPLL is modeled like logical deduction
--   LHS: a set of assumptions / partial model (conjunction of literals)
--   RHS: A set of goals in conjunctive normal form
data Sequent p = ConstraintProblem p :|-: CNF p

{- Goal Reduction Rules -}

-- | Unit Propogation
--   Takes literals `L` and sequent `A :|-: B` to `L ∪ A :|-: B'`
--   where `B'` is defined by
--    * Every instance of `¬x` is removed from all clauses in B for all `x ∈ L`
--    * All clauses in `B` containing some `x ∈ L` are removed
unitPropogate :: Ord p => ConstraintProblem p -> Sequent p -> Sequent p
unitPropogate literals (assms :|-: clauses) =
  let resolve = Data.Set.map (\\ Data.Set.map neg literals)
      filterSatisfied =
        Data.Set.filter (Data.Set.null . (literals `Data.Set.intersection`))
  in  (literals <> assms) :|-: filterSatisfied (resolve clauses)

-- | Pure Rule
--   A literal is said to be _pure_ in a CNF if all instances have the same sign
--   (either all `Pos` or all `Neg`).
--   This rule finds all pure literals and performs unit propogation on them
pureRule :: (Ord p, Alternative f) => Sequent p -> f (Sequent p)
pureRule sequent@(_ :|-: clauses) =
  let
    sign (Pos _) = True
    sign (Neg _) = False
    -- Partition the positive and negative formulae
    (positive, negative) = Data.Set.partition sign (Data.Foldable.fold clauses)
    -- Compute the literals that are purely positive/negative
    purePos              = positive \\ Data.Set.map neg negative
    pureNeg              = negative \\ Data.Set.map neg positive
  in
    if Data.Set.null purePos && Data.Set.null pureNeg
      then empty
      else (pure . unitPropogate (purePos <> pureNeg)) sequent

-- | One Rule
--   If a clause `{x}` occurs in a CNF, add the clause to the assumptions
--   and perform unit propogation to eliminate the literal `x`
oneRule :: (Ord p, Alternative f) => Sequent p -> f (Sequent p)
oneRule sequent@(_ :|-: clauses) =
  let isSingleton c = Data.Set.size c == 1
      singletons = (Data.Foldable.fold . Data.Set.filter isSingleton) clauses
  in  if null singletons
        then empty
        else (pure . unitPropogate singletons) sequent

{- Core Search Algorithm -}

-- | Answer-Sat using DPLL
--   By using an underlying model search procedure for conjuncts of clauses
--   DPLL can be used to lift that procedure to CNFs of clauses
instance ( Ord l
         , MonadPlus m
         , ConstrainedModelSearch d l m )
         => ModelSearch d (CNF l) m
  where
  findModel goalClauses = dpll $ mempty :|-: goalClauses
    where
      dpll sequent@(assms :|-: clauses) = do
        -- Fail early if falsum is a subgoal
        guard $ not (mempty `Data.Set.member` clauses)
        case Data.Foldable.concatMap Data.Set.toList clauses of
          -- If DPLL has terminated, attempt to solve the new constraint problem
          []  -> findConstrainedModel assms
          -- Otherwise try various tactics for resolving goals
          x:_ -> dpll =<< msum
            [ pureRule sequent
            , oneRule sequent
            , return (unitPropogate (Data.Set.singleton x) sequent)
            , return (unitPropogate ((Data.Set.singleton . neg) x) sequent)
            ]
