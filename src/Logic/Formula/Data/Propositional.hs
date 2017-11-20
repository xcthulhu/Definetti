module Logic.Formula.Data.Propositional ( Propositional(..) ) where

-- | Propositional formulae
infixr 8 :->:
data Propositional a = Proposition a
                     | (Propositional a) :&: (Propositional a)
                     | (Propositional a) :|: (Propositional a)
                     | (Propositional a) :->: (Propositional a)
                     | Not (Propositional a)
                     | Verum
                     | Falsum
                     deriving (Ord, Show, Eq)
