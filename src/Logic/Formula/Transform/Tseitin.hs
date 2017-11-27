module Logic.Formula.Transform.Tseitin (definitionalClauses) where

import           Control.Monad.State
import qualified Data.Set                         as Set
import           Logic.Formula.Data.Literal
import           Logic.Formula.Data.Propositional

getFreshDefinitionalLiteral :: State Int (Definitional a)
getFreshDefinitionalLiteral =
  do lastVar <- get
     let freshVar = lastVar + 1
     put freshVar
     return $ Definition freshVar

getLastDefinitionalLiteral :: State Int (Definitional a)
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

defineSubClause ::
  Ord a =>
  Propositional a ->
  State Int (Set.Set (Clause (Definitional a)))
defineSubClause (Proposition a) =
  do fresh <- getFreshDefinitionalLiteral
     return $ set2 (set2 (Neg fresh)    (Pos (Atom a)))
                   (set2 (Neg (Atom a)) (Pos fresh))

defineSubClause (Not (Proposition a)) =
  do fresh <- getFreshDefinitionalLiteral
     return $ set2 (set2 (Neg fresh)    (Neg (Atom a)))
                   (set2 (Pos (Atom a)) (Pos fresh))

defineSubClause (Not a) =
  do clause <- defineSubClause a
     notADef <- getLastDefinitionalLiteral
     fresh <- getFreshDefinitionalLiteral
     return $
       Set.fromList [set2 (Neg fresh) (Pos notADef), set2 (Neg notADef) (Pos fresh)] `mappend` clause

defineSubClause (a :&: b) =
  do aMaxSatClause <- defineSubClause a
     aDef <- getLastDefinitionalLiteral
     bMaxSatClause <- defineSubClause b
     bDef <- getLastDefinitionalLiteral
     fresh <- getFreshDefinitionalLiteral
     return $
       Set.fromList [ Set.fromList [Neg fresh, Pos aDef]
                      , Set.fromList [Neg fresh, Pos bDef]
                      , Set.fromList [Neg aDef, Neg bDef, Pos fresh]]
       `mappend` aMaxSatClause `mappend` bMaxSatClause

defineSubClause (a :|: b) =
  do aMaxSatClause <- defineSubClause a
     a_ <- getLastDefinitionalLiteral
     bMaxSatClause <- defineSubClause b
     b_ <- getLastDefinitionalLiteral
     c_ <- getFreshDefinitionalLiteral
     return $
       Set.fromList [ Set.fromList [Neg c_, Pos a_, Pos b_]
                    , Set.fromList [Neg a_, Pos c_]
                    , Set.fromList [Neg b_, Pos c_]]
       `mappend` aMaxSatClause `mappend` bMaxSatClause

defineSubClause (a :->: b) = defineSubClause (Not a :|: b)

defineSubClause Verum =
  do a_ <- getFreshDefinitionalLiteral
     return ( Set.fromList [Set.fromList [Pos a_]] )

defineSubClause Falsum =
  do a_ <- getFreshDefinitionalLiteral
     return ( Set.fromList [Set.fromList [Neg a_]] )

defineClause ::
  Ord a =>
  Propositional a ->
  State Int (Set.Set (Clause (Definitional a)))
defineClause f =
  do subFormulaClauses <- defineSubClause f
     top <- getLastDefinitionalLiteral
     return ( Set.insert (Set.fromList [Pos top]) subFormulaClauses )

definitionalClauses ::
  Ord a =>
  [Propositional a] ->
  [Set.Set (Clause (Definitional a))]
definitionalClauses propositions =
  evalState (mapM defineClause propositions) 0
