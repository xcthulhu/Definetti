module Logic.Formula.Transform.Tseitin ( tseitinSoft, tseitinHard ) where

import           Control.Monad.State
import qualified Data.DList                       as DList
import qualified Data.Set                         as Set
import           Logic.Formula.Data.Literal
import           Logic.Formula.Data.MaxSatClause
import           Logic.Formula.Data.Propositional

freshVar :: State Int Int
freshVar =
  do lastVar <- get
     let newVar = lastVar + 1
     put newVar
     return newVar

defineHardSubClause :: Ord a => Propositional a -> State Int (DList.DList (MaxSatClause (Definitional a)))
defineHardSubClause (Proposition a) =
  do let a_ = Atom a
     newVar <- freshVar
     let b_ = Definition newVar
     return $ DList.fromList [Hard (Set.fromList [Neg b_, Pos a_]), Hard (Set.fromList [Neg a_, Pos b_])]

defineHardSubClause (Not (Proposition a)) =
  do let a_ = Atom a
     newVar <- freshVar
     let b_ = Definition newVar
     return $ DList.fromList [Hard (Set.fromList [Neg b_, Neg a_]), Hard (Set.fromList [Pos a_, Pos b_])]

defineHardSubClause (Not a) =
  do clause <- defineHardSubClause a
     aVar <- get
     let a_ = Definition aVar
     newVar <- freshVar
     let b_ = Definition newVar
     return $
       DList.fromList [Hard (Set.fromList [Neg b_, Pos a_]), Hard (Set.fromList [Neg a_, Pos b_])] `mappend` clause

defineHardSubClause (a :&: b) =
  do aMaxSatClause <- defineHardSubClause a
     aVar <- get
     let a_ = Definition aVar
     bMaxSatClause <- defineHardSubClause b
     bVar <- get
     let b_ = Definition bVar
     newVar <- freshVar
     let c_ = Definition newVar
     return $
       DList.fromList [ Hard (Set.fromList [ Neg c_, Pos a_ ])
                      , Hard (Set.fromList [ Neg c_, Pos b_ ])
                      , Hard (Set.fromList [ Neg a_, Neg b_, Pos c_ ]) ]
       `mappend` aMaxSatClause `mappend` bMaxSatClause

defineHardSubClause (a :|: b) =
  do aMaxSatClause <- defineHardSubClause a
     aVar <- get
     let a_ = Definition aVar
     bMaxSatClause <- defineHardSubClause b
     bVar <- get
     let b_ = Definition bVar
     newVar <- freshVar
     let c_ = Definition newVar
     return $
       DList.fromList [ Hard (Set.fromList [ Neg c_, Pos a_, Pos b_ ])
                       , Hard (Set.fromList [ Neg a_, Pos c_ ])
                       , Hard (Set.fromList [ Neg b_, Pos c_ ]) ]
       `mappend` aMaxSatClause `mappend` bMaxSatClause

defineHardSubClause (a :->: b) = defineHardSubClause (Not a :|: b)
defineHardSubClause Verum =
  do newVar <- freshVar
     return $ DList.fromList [ Hard (Set.fromList [Pos (Definition newVar)])]
defineHardSubClause Falsum =
  do newVar <- freshVar
     return $ DList.fromList [ Hard (Set.fromList [Neg (Definition newVar)])]

defineSoftClause :: Ord a => Propositional a -> State Int (DList.DList (MaxSatClause (Definitional a)))
defineSoftClause f =
  do hardMaxSatClauses <- defineHardSubClause f
     lastVar <- get
     return $ return (Soft (Set.fromList [Pos (Definition lastVar)])) `mappend` hardMaxSatClauses

defineHardClause :: Ord a => Propositional a -> State Int (DList.DList (MaxSatClause (Definitional a)))
defineHardClause f =
  do hardMaxSatClauses <- defineHardSubClause f
     lastVar <- get
     return $ return (Hard (Set.fromList [Pos (Definition lastVar)])) `mappend` hardMaxSatClauses

tseitinSoft :: Ord a => [Propositional a] -> [MaxSatClause (Definitional a)]
tseitinSoft forms =
  let formDCNFDefinitions = map defineSoftClause forms
      dCNFDLists = evalState (sequence formDCNFDefinitions) 0
  in DList.toList $ mconcat dCNFDLists

tseitinHard :: Ord a => [Propositional a] -> Set.Set (MaxSatClause (Definitional a))
tseitinHard forms =
  let formDCNFDefinitions = map defineHardClause forms
      dCNFDLists = evalState (sequence formDCNFDefinitions) 0
  in (Set.fromList . DList.toList . mconcat) dCNFDLists
