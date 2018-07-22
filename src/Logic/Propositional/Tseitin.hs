{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module Logic.Propositional.Tseitin
  ( Propositional ( (:&&:)
                  , (:->:)
                  , (:||:)
                  , Falsum
                  , Not
                  , Proposition
                  , Verum )
  , tseitinTransform
  , Definitional
  ) where

import           Control.Monad            (MonadPlus)
import           Data.Monoid              (mempty, (<>))
import qualified Data.Set                 (Set, insert, singleton)

import           Logic.Propositional.DPLL (CNF, ConstrainedModelSearch,
                                           Literal (Neg, Pos),
                                           findConstrainedModel)
import           Logic.Semantics          (ModelSearch (findModel),
                                           Semantics ((|=)))


-- | Formulae of the Propositional Calculus
infixr 8 :->:
data Propositional p = Proposition p
                     | (Propositional p) :&&: (Propositional p)
                     | (Propositional p) :||: (Propositional p)
                     | (Propositional p) :->: (Propositional p)
                     | Not (Propositional p)
                     | Verum
                     | Falsum
                     deriving (Ord, Show, Eq)

-- | Semantics for the Propositional Calculus
instance Semantics d p => Semantics d (Propositional p) where
  m |= (Proposition p) = m |= p
  m |= (f :&&: g)      = (m |= f) && (m |= g)
  m |= (f :||: g)      = (m |= f) || (m |= g)
  m |= (f :->: g)      = not (m |= f) || (m |= g)
  m |= (Not f)         = not (m |= f)
  _ |= Verum           = True
  _ |= Falsum          = False

-- | Definitional Atoms
--
-- Inspired by John Harrison's
-- "Handbook of Practical Logic and Automated Reasoning" (2009),
-- Section 2.8, pgs. 75-77
--
-- Note:
--   Definitional literals use the propositions they represent themselves
--   as labels.
--
--   This is a _referentially transparent_ means of creating labels,
--   however it differs from Harrison's method (which uses a counter as state).

data Definitional p =
    Definition (Propositional p)  -- ^ a literal that defines a subterm
  | Atom p                        -- ^ a literal for an atomic proposition
    deriving (Ord, Show, Eq)

-- | ConstrainedModelSearch for Conjunctions of Literals of Definitional Atoms
-- When finding a model for a conjunction of literals of definitional atoms,
-- model search proceeds ignoring the definitional atoms.

instance ( Ord p
         , MonadPlus m
         , ConstrainedModelSearch d p m )
         => ConstrainedModelSearch d (Definitional p) m
  where
    findConstrainedModel definitionals = findConstrainedModel atoms
      where
        atoms = foldr extractAtoms mempty definitionals
        extractAtoms (Pos (Atom a)) = Data.Set.insert (Pos a)
        extractAtoms (Neg (Atom a)) = Data.Set.insert (Neg a)
        extractAtoms _              = id

{---------------------------- Tseitin Transformation ------------------------}

{-
 - Propositional Formulae can be converted to CNFs of definitional literals.
 - This is done via the _Tseitin Transformation_.
 -
 - _Answer-Sat_ is defined for propositional formulae using this conversion.
 -
 - Once a propositional formula is converted to a CNF, DPLL-based Answer-Sat
 - can be leveraged.
 -
 - DPLL-based Answer-Sat is defined in the `CNF` module.
 -}

insert2 :: Ord p => p -> p -> Data.Set.Set p -> Data.Set.Set p
insert2 x y set = Data.Set.insert x (Data.Set.insert y set)

insert3 :: Ord p => p -> p -> p -> Data.Set.Set p -> Data.Set.Set p
insert3 x y z set = Data.Set.insert x (insert2 y z set)

set2 :: Ord p => p -> p -> Data.Set.Set p
set2 x y = insert2 x y mempty

set3 :: Ord p => p -> p -> p -> Data.Set.Set p
set3 x y z = insert3 x y z mempty

definitionalSubClauses :: Ord p => Propositional p -> CNF (Definitional p)

definitionalSubClauses f@(Proposition a) =
  let (f', a') = (Definition f, Atom a)
  in  set2 (set2 (Neg f') (Pos a')) (set2 (Neg a') (Pos f'))

definitionalSubClauses f@(Not g) =
  let (f', g') = (Definition f, Definition g)
  in  insert2 (set2 (Neg f') (Neg g'))
              (set2 (Pos f') (Pos g'))
              (definitionalSubClauses g)

definitionalSubClauses f@(g:&&:h) =
  let (f', g', h') = (Definition f, Definition g, Definition h)
  in  insert3 (set2 (Neg f') (Pos g'))
              (set2 (Neg f') (Pos h'))
              (set3 (Neg g') (Neg h') (Pos f'))
              (definitionalSubClauses g <> definitionalSubClauses h)

definitionalSubClauses f@(g:||:h) =
  let (f', g', h') = (Definition f, Definition g, Definition h)
  in  insert3 (set3 (Neg f') (Pos g') (Pos h'))
              (set2 (Neg g') (Pos f'))
              (set2 (Neg h') (Pos f'))
              (definitionalSubClauses g <> definitionalSubClauses h)

definitionalSubClauses f@(g:->:h) =
  let (f', g', h') = (Definition f, Definition g, Definition h)
  in  insert3 (set3 (Neg f') (Neg g') (Pos h'))
              (set2 (Pos g') (Pos f'))
              (set2 (Neg h') (Pos f'))
              (definitionalSubClauses g <> definitionalSubClauses h)

definitionalSubClauses Verum =
  (Data.Set.singleton . Data.Set.singleton . Pos . Definition) Verum

definitionalSubClauses Falsum =
  (Data.Set.singleton . Data.Set.singleton . Neg . Definition) Falsum

tseitinTransform :: Ord p => Propositional p -> CNF (Definitional p)
tseitinTransform f = Data.Set.insert
  (Data.Set.singleton (Pos (Definition f)))
  (definitionalSubClauses f)

-- | Propositional Formula Answer-Sat
-- By converting propositional formulae to (definitional) CNF,
-- existing DPLL-based Answer-Sat can be used for the propositional calculus
instance ( Ord p
         , MonadPlus m
         , ConstrainedModelSearch d p m )
         => ModelSearch d (Propositional p) m
  where
    findModel = findModel . tseitinTransform
