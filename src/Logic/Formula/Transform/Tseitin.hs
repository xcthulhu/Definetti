{-# LANGUAGE RecordWildCards #-}
module Logic.Formula.Transform.Tseitin (definitionalClauses) where

import           Control.Monad.State
import qualified Data.Set                         as Set
import           Logic.Formula.Data.Literal
import           Logic.Formula.Data.Propositional

dualize :: Propositional a -> Propositional a
dualize (Proposition a) = Not (Proposition a)
dualize (Not p) = p
dualize (x :&: y) = dualize x :|: dualize y
dualize (x :|: y) = dualize x :&: dualize y
dualize (x :->: y) = x :&: dualize y
dualize Verum = Falsum
dualize Falsum = Verum

type Idx = Int
initialIdx :: Idx
initialIdx = 0

getFreshDefinitionalLiteral :: State Idx (Definitional a)
getFreshDefinitionalLiteral =
  do lastVar <- get
     let freshVar = lastVar + 1
     put freshVar
     return $ Definition freshVar

getLastDefinitionalLiteral :: State Idx (Definitional a)
getLastDefinitionalLiteral = fmap Definition get

insert2 :: Ord a => a -> a -> Set.Set a -> Set.Set a
insert2 x y set = Set.insert x (Set.insert y set)

insert3 :: Ord a => a -> a -> a -> Set.Set a -> Set.Set a
insert3 x y z set = Set.insert x (Set.insert y (Set.insert z set))

set2 :: Ord a => a -> a -> Set.Set a
set2 x y = insert2 x y Set.empty

set3 :: Ord a => a -> a -> a -> Set.Set a
set3 x y z = insert3 x y z Set.empty

data PairClauses a = PairClauses { xDef :: a
                                 , yDef :: a
                                 , fresh :: a
                                 , xyCombinedClauses :: Set.Set (Clause a)
                                 }

extractPairClausesDefinitions
  :: Ord a
  => Propositional a
  -> Propositional a
  -> State Int (PairClauses (Definitional a))
extractPairClausesDefinitions x y =
  do xClauses <- defineSubClause x
     xDef <- getLastDefinitionalLiteral
     yClauses <- defineSubClause y
     yDef <- getLastDefinitionalLiteral
     fresh <- getFreshDefinitionalLiteral
     return $ PairClauses xDef yDef fresh (xClauses `mappend` yClauses)

defineSubClause
  :: Ord a
  => Propositional a
  -> State Int (Set.Set (Clause (Definitional a)))
defineSubClause (Proposition a) =
  do fresh <- getFreshDefinitionalLiteral
     return (set2 (set2 (Neg fresh)    (Pos (Atom a)))
                  (set2 (Neg (Atom a)) (Pos fresh)))

defineSubClause (Not (Proposition a)) =
  do fresh <- getFreshDefinitionalLiteral
     return (set2 (set2 (Neg fresh)    (Neg (Atom a)))
                  (set2 (Pos (Atom a)) (Pos fresh)))

defineSubClause (Not a) = defineSubClause (dualize a)

defineSubClause (a :&: b) =
  do PairClauses {..} <- extractPairClausesDefinitions a b
     return (insert3 (set2 (Neg fresh) (Pos xDef))
                     (set2 (Neg fresh) (Pos yDef))
                     (set3 (Neg xDef)  (Neg yDef) (Pos fresh))
                     xyCombinedClauses)

defineSubClause (a :|: b) =
  do PairClauses {..} <- extractPairClausesDefinitions a b
     return (insert3 (set3 (Neg fresh) (Pos xDef) (Pos yDef))
                     (set2 (Neg xDef)  (Pos fresh))
                     (set2 (Neg yDef)  (Pos fresh))
                     xyCombinedClauses)

defineSubClause (a :->: b) =
  do PairClauses {..} <- extractPairClausesDefinitions a b
     return (insert3 (set3 (Neg fresh) (Neg xDef) (Pos yDef))
                     (set2 (Pos xDef)  (Pos fresh))
                     (set2 (Neg yDef)  (Pos fresh))
                     xyCombinedClauses)

defineSubClause Verum =
  fmap ( Set.singleton . Set.singleton . Pos ) getFreshDefinitionalLiteral

defineSubClause Falsum =
  fmap ( Set.singleton . Set.singleton . Neg ) getFreshDefinitionalLiteral

defineClause ::
  Ord a =>
  Propositional a ->
  State Idx (Set.Set (Clause (Definitional a)))
defineClause f =
  do subFormulaClauses <- defineSubClause f
     top <- getLastDefinitionalLiteral
     return ( Set.insert (Set.fromList [Pos top]) subFormulaClauses )

definitionalClauses ::
  Ord a =>
  [Propositional a] ->
  [Set.Set (Clause (Definitional a))]
definitionalClauses propositions =
  evalState (mapM defineClause propositions) initialIdx

