{-# LANGUAGE RecordWildCards #-}
module Logic.Formula.Transform.Tseitin (definitionalClauses) where

import           Control.Monad.State
import qualified Data.Set                         as Set
import           Logic.Formula.Data.Literal
import           Logic.Formula.Data.Propositional

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
getLastDefinitionalLiteral =
  do lastVar <- get
     return $ Definition lastVar

insert2 :: Ord a => a -> a -> Set.Set a -> Set.Set a
insert2 x y set = Set.insert x (Set.insert y set)

insert3 :: Ord a => a -> a -> a -> Set.Set a -> Set.Set a
insert3 x y z set = Set.insert x (Set.insert y (Set.insert z set))

set2 :: Ord a => a -> a -> Set.Set a
set2 x y = insert2 x y Set.empty

set3 :: Ord a => a -> a -> a -> Set.Set a
set3 x y z = insert3 x y z Set.empty

data PairClauses a = PairClauses { aDef :: a
                                 , bDef :: a
                                 , fresh :: a
                                 , abCombinedClauses :: Set.Set (Clause a)
                                 }

extractPairClausesDefinitions
  :: Ord a
  => Propositional a
  -> Propositional a
  -> State Int (PairClauses (Definitional a))
extractPairClausesDefinitions a b =
  do aClauses <- defineSubClause a
     aDef <- getLastDefinitionalLiteral
     bClauses <- defineSubClause b
     bDef <- getLastDefinitionalLiteral
     fresh <- getFreshDefinitionalLiteral
     return $ PairClauses aDef bDef fresh (aClauses `mappend` bClauses)

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

defineSubClause (Not a) =
  do aClauses <- defineSubClause a
     aDef <- getLastDefinitionalLiteral
     fresh <- getFreshDefinitionalLiteral
     return (insert2 (set2 (Neg fresh) (Neg aDef))
                     (set2 (Pos aDef)  (Pos fresh))
                     aClauses)


defineSubClause (a :&: b) =
  do PairClauses {..} <- extractPairClausesDefinitions a b
     return (insert3 (set2 (Neg fresh) (Pos aDef))
                     (set2 (Neg fresh) (Pos bDef))
                     (set3 (Neg aDef)  (Neg bDef) (Pos fresh))
                     abCombinedClauses)

defineSubClause (a :|: b) =
  do PairClauses {..} <- extractPairClausesDefinitions a b
     return (insert3 (set3 (Neg fresh) (Pos aDef) (Pos bDef))
                     (set2 (Neg aDef)  (Pos fresh))
                     (set2 (Neg bDef)  (Pos fresh))
                     abCombinedClauses)

defineSubClause (a :->: b) =
  do PairClauses {..} <- extractPairClausesDefinitions a b
     return (insert3 (set3 (Neg fresh) (Neg aDef) (Pos bDef))
                     (set2 (Pos aDef)  (Pos fresh))
                     (set2 (Neg bDef)  (Pos fresh))
                     abCombinedClauses)

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
