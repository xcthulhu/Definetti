module Logic.Satisfaction.PropositionalSat (dpllProposition) where
import           Control.Monad                    (MonadPlus)
import qualified Data.Set                         as Set
import           Logic.Formula.Data.Literal
import           Logic.Formula.Data.Propositional
import           Logic.Formula.Transform.Tseitin  (definitionalClauses)
import           Logic.Satisfaction.Sat


extractModelFromDPLLSat :: Ord a => Set.Set (Definitional a) -> Set.Set a
extractModelFromDPLLSat = Set.fold addAtom Set.empty
  where
    addAtom (Atom a) collectedAtoms       = Set.insert a collectedAtoms
    addAtom (Definition _) collectedAtoms = collectedAtoms

tseitinProposition :: Ord a => Propositional a -> Set.Set (Clause (Definitional a))
tseitinProposition = Set.unions . definitionalClauses . (:[])

dpllProposition
  :: (Ord a, MonadPlus m)
  => Propositional a
  -> m (Set.Set  a)
dpllProposition = fmap extractModelFromDPLLSat . dpll . tseitinProposition
