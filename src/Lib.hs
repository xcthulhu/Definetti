module Lib ( tseitinSoft ) where

import Formula.Data.PropForm
import Formula.Data.DLiteral
import Formula.Data.Clause
import Control.Monad.State
import qualified Data.DList as DList

freshVar :: State Int Int
freshVar =
  do lastVar <- get
     let newVar = lastVar + 1
     put newVar
     return newVar

defineHardSubClause :: PropForm a -> State Int (DList.DList (Clause a))
defineHardSubClause (Atom a) =
  do newVar <- freshVar
     return $ DList.fromList [ Hard [Neg (Left newVar), Pos (Right a)]
                             , Hard [Neg (Right a), Pos (Left newVar)]]
defineHardSubClause (Not (Atom a)) =
  do newVar <- freshVar
     return $ DList.fromList [ Hard [Neg (Left newVar), Neg (Right a) ]
                             , Hard [Pos (Right a), Pos (Left newVar) ] ]
defineHardSubClause (Not a) =
  do clause <- defineHardSubClause a
     lastVar <- get
     newVar <- freshVar
     return $
       (DList.fromList [ Hard [ Neg (Left newVar), Neg (Left lastVar) ]
                       , Hard [ Pos (Left newVar), Pos (Left lastVar) ] ])
       `mappend` clause
defineHardSubClause (a :&: b) =
  do aClause <- defineHardSubClause a
     aVar <- get
     bClause <- defineHardSubClause b
     bVar <- get
     newVar <- freshVar
     return $
       (DList.fromList [ Hard [ Neg (Left newVar), Pos (Left aVar) ]
                       , Hard [ Neg (Left newVar), Pos (Left bVar) ]
                       , Hard [ Neg (Left aVar)
                              , Neg (Left bVar)
                              , Pos (Left newVar) ] ])
       `mappend` aClause `mappend` bClause
defineHardSubClause (a :|: b) =
  do aClause <- defineHardSubClause a
     aVar <- get
     bClause <- defineHardSubClause b
     bVar <- get
     newVar <- freshVar
     return $
       (DList.fromList [ Hard [ Neg (Left newVar)
                              , Pos (Left aVar)
                              , Pos (Left bVar) ]
                       , Hard [ Neg (Left aVar), Pos (Left newVar) ]
                       , Hard [ Neg (Left bVar), Pos (Left newVar) ] ])
       `mappend` aClause `mappend` bClause
defineHardSubClause (a :->: b) = defineHardSubClause (Not a :|: b)
defineHardSubClause Verum =
  do newVar <- freshVar
     return $ DList.fromList [ Hard [Pos (Left newVar)]]
defineHardSubClause Falsum =
  do newVar <- freshVar
     return $ DList.fromList [ Hard [Neg (Left newVar)]]

defineSoftClause :: PropForm a -> State Int (DList.DList (Clause a))
defineSoftClause f =
  do hardClauses <- defineHardSubClause f
     lastVar <- get
     return $ (return $ Soft [(Pos (Left lastVar))]) `mappend` hardClauses

defineHardClause :: PropForm a -> State Int (DList.DList (Clause a))
defineHardClause f =
  do hardClauses <- defineHardSubClause f
     lastVar <- get
     return $ (return $ Hard [(Pos (Left lastVar))]) `mappend` hardClauses

tseitinSoft :: [PropForm a] -> [Clause a]
tseitinSoft forms =
  let formDCNFDefinitions = map defineSoftClause forms
      dCNFDLists = evalState (sequence formDCNFDefinitions) 0
  in DList.toList $ mconcat dCNFDLists

tseitinHard :: [PropForm a] -> [Clause a]
tseitinHard forms =
  let formDCNFDefinitions = map defineHardClause forms
      dCNFDLists = evalState (sequence formDCNFDefinitions) 0
  in DList.toList $ mconcat dCNFDLists
