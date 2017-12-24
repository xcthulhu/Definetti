module Logic.Formula.Transform.Tseitin (definitionalClauses) where

import qualified Data.Set                         as Set
import           Logic.Formula.Data.Literal
import           Logic.Formula.Data.Propositional

insert2 :: Ord a => a -> a -> Set.Set a -> Set.Set a
insert2 x y set = Set.insert x (Set.insert y set)

insert3 :: Ord a => a -> a -> a -> Set.Set a -> Set.Set a
insert3 x y z set = Set.insert x (Set.insert y (Set.insert z set))

set2 :: Ord a => a -> a -> Set.Set a
set2 x y = insert2 x y Set.empty

set3 :: Ord a => a -> a -> a -> Set.Set a
set3 x y z = insert3 x y z Set.empty

definitionalSubClauses
  :: Ord a
  => Propositional a
  -> Set.Set (Clause (Definitional a))

definitionalSubClauses p@(Proposition a) =
  let p' = Definition p
  in set2 (set2 (Neg p')       (Pos (Atom a)))
          (set2 (Neg (Atom a)) (Pos p'))

definitionalSubClauses (Not p) =
  let np' = Definition (Not p)
      p' = Definition p
  in insert2 (set2 (Neg np') (Neg p'))
             (set2 (Pos np') (Pos p'))
             (definitionalSubClauses p)

definitionalSubClauses p@(a :&: b) =
  let (p', a', b') = (Definition p, Definition a, Definition b)
  in insert3 (set2 (Neg p') (Pos a'))
             (set2 (Neg p') (Pos b'))
             (set3 (Neg a') (Neg b') (Pos p'))
             (definitionalSubClauses a `Set.union` definitionalSubClauses b)

definitionalSubClauses p@(a :|: b) =
  let (p', a', b') = (Definition p, Definition a, Definition b)
  in insert3 (set3 (Neg p') (Pos a') (Pos b'))
             (set2 (Neg a') (Pos p'))
             (set2 (Neg b') (Pos p'))
             (definitionalSubClauses a `Set.union` definitionalSubClauses b)

definitionalSubClauses p@(a :->: b) =
  let (p', a', b') = (Definition p, Definition a, Definition b)
  in insert3 (set3 (Neg p') (Neg a') (Pos b'))
             (set2 (Pos a')  (Pos p'))
             (set2 (Neg b')  (Pos p'))
             (definitionalSubClauses a `Set.union` definitionalSubClauses b)

definitionalSubClauses Verum =
  (Set.singleton . Set.singleton . Pos . Definition) Verum

definitionalSubClauses Falsum =
  (Set.singleton . Set.singleton . Neg . Definition) Falsum

definitionalClauses
   :: Ord a
   => [Propositional a]
   -> [Set.Set (Clause (Definitional a))]
definitionalClauses =
  map (\p -> Set.insert (Set.singleton (Pos (Definition p)))
                        (definitionalSubClauses p))
