{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MonoLocalBinds        #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RecordWildCards       #-}

module Logic.Probability
  ( Probability (Pr, Const, (:+), (:*))
  , ProbabilityInequality ((:<), (:>), (:>=), (:<=))
  , count
  ) where

import           Control.Applicative         (Alternative, empty, pure, (<|>))
import           Control.Arrow               (first, second, (***))
import           Control.Monad               (MonadPlus, msum)
import qualified Data.Foldable               (fold)
import           Data.List                   (partition)
import           Data.List.NonEmpty          (NonEmpty)
import qualified Data.Map                    as Map
import           Data.Monoid                 ((<>))
import           Data.Ratio                  (denominator, (%))

import           Logic.Propositional         (Propositional (Not))
import           Logic.Propositional.DPLL    (CNF, ConstrainedModelSearch)
import           Logic.Propositional.Tseitin (tseitinTransform)
import           Logic.Semantics             (ModelSearch (findModel),
                                              Semantics ((|=)))

-- | Probability Inequalities
data Probability p = Pr (Propositional p)
                   | Const Rational
                   | (Probability p) :+ (Probability p)
                   | Rational        :* (Probability p)
                   deriving (Ord, Show, Eq)

data ProbabilityInequality p = (Probability p) :<  (Probability p)
                             | (Probability p) :>  (Probability p)
                             | (Probability p) :>= (Probability p)
                             | (Probability p) :<= (Probability p)
                             deriving (Ord, Show, Eq)

count :: (Foldable t, Integral n) => (a -> Bool) -> t a -> n
count p = foldr (\a c -> if p a then c + 1 else c) 0

evalProbability :: Semantics d p => NonEmpty d -> Probability p -> Rational
evalProbability _ (Const c) = c
evalProbability m (Pr p)    = count (|= p) m % (toInteger . length) m
evalProbability m (x :+ y)  = evalProbability m x + evalProbability m y
evalProbability m (a :* x)  = a * evalProbability m x

instance Semantics d p => Semantics (NonEmpty d) (ProbabilityInequality p) where
  m |= (a :< b)  = evalProbability m a <  evalProbability m b
  m |= (a :<= b) = evalProbability m a <= evalProbability m b
  m |= (a :>= b) = evalProbability m a >= evalProbability m b
  m |= (a :> b)  = evalProbability m a >  evalProbability m b

-- | Normal form for probabilistic inequalities / Trades
-- Represents equations of the form:
-- `w1 * a1 + w2 * a2 + ... + C </<= v1 * b1 + v2 * b2 + ...`
-- here `</<=` is either strict or non-strict inequality

data GTSummationNormalForm a =
  GTSummationNormalForm { leftHandTerms    :: [(a, Rational)]
                        , leftHandConstant :: Rational
                        , rightHandTerms   :: [(a, Rational)]
                        , strict           :: Bool }


add :: (Ord p, Num n) => Map.Map p n -> Map.Map p n -> Map.Map p n
add = Map.unionWith (+)

extractPropositions :: Ord p
                    => Probability p
                    -> Map.Map (Propositional p) Rational
extractPropositions (Pr p)    = Map.singleton p 1
extractPropositions (Const _) = Map.empty
extractPropositions (x :+ y)  =
  extractPropositions x `add` extractPropositions y
extractPropositions (a :* x)  =
  Map.map (a *) (extractPropositions x)

extractConstantTerm :: Probability p
                    -> Rational
extractConstantTerm (Pr _)    = 0
extractConstantTerm (Const d) = d
extractConstantTerm (x :+ y)  = extractConstantTerm x + extractConstantTerm y
extractConstantTerm (a :* x)  = a * extractConstantTerm x

summationNormalForm :: Ord p
                    => ProbabilityInequality p
                    -> GTSummationNormalForm (Propositional p)
summationNormalForm (b :>  a) = summationNormalForm (a :<  b)
summationNormalForm (b :>= a) = summationNormalForm (a :<= b)
summationNormalForm (a :< b)  = (summationNormalForm (a :<= b)) {strict = True}
summationNormalForm (a :<= b) =
  GTSummationNormalForm
  { leftHandTerms = lhts
  , leftHandConstant = extractConstantTerm a - extractConstantTerm b
  , rightHandTerms = rhts
  , strict = False }
  where
    x `minus` y = x `add` Map.map negate y
    weightedTerms =
      Map.toList $ extractPropositions a `minus` extractPropositions b
    (lhts, rhts) =
        second (fmap (second negate))
      . partition ((>0) . snd)
      . filter ((/= 0) . snd)
      $ weightedTerms


-- | Choose `k` elements of a collection of weighted elements with
--   specified total weight. In the event that all elements have weight 1,
--   this results in exactly
--   `totalWeight choose k = totalWeight! / (k!(totalWeight-k)!)`
--   possible choices.
--   Lifted into an arbitrary `Alternative` functor;
--   using `List` results in a list of all of the possible choices.
weightedChoose :: Alternative f
               => [(a, Integer)]
               -> Integer
               -> Integer
               -> f [a]
weightedChoose clauses totalWeight k
  | k > totalWeight             = empty
  | k <= 0                      = pure []
  | k == totalWeight            = pure (map fst clauses)
  | [] <- clauses               = error "This should never happen"
  | ((x, weight):xs) <- clauses =
  let totalWeight' = totalWeight - weight
  in weightedChoose xs totalWeight' k <|>
     fmap (x :) (weightedChoose xs totalWeight' (k - weight))

-- | Determine if the largest sublist of CNFs simultaneously satisfiable
--   has weight no bigger than `k`
maxSatN :: (Ord a, MonadPlus m, ModelSearch d (CNF a) m)
        => Integer
        -> [(CNF a, Integer)]
        -> m d
maxSatN k = msum . fmap (findModel . Data.Foldable.fold) . chooseN
 where
   totalWeight = sum . fmap snd
   chooseN :: [(CNF a, Integer)] -> [[CNF a]]
   chooseN xs = weightedChoose xs (totalWeight xs) (k + 1)

-- | Model search for probabilistic inequalities in 'GTSummationNormalForm'
--   This makes use of the law
--
-- \[
-- \begin{align*}
-- \Sum_{i \in I} c_i \cdot P(\phi_i) + A & \leq \Sum_{j \in J} k_j \cdot P(\psi_j) + B \\
--                                        & \equiv \\
-- \mathrm{WeightedMaxSat}(\{ (\hat{c}_i, \phi_i)\ : \ i \in I \}
--                         \cup \{ (\hat{d}_j, \psi_j)\ :\ j \in J \}) & \leq \hat{B} - \hat{A}
-- \end{align*}
-- \]
--
-- where \(\hat{x}\) is \(x\) times the least common multiple
-- of the denominators of all of coefficients and constants.
instance ( Ord p
         , MonadPlus m
         , ConstrainedModelSearch d p m )
         => ModelSearch (NonEmpty d) (GTSummationNormalForm (Propositional p)) m
  where
    findModel GTSummationNormalForm {..} =
      pure <$> maxSatN (floor k) clauses where
        allTerms = leftHandTerms <> rightHandTerms
        denominatorProduct =
          fromIntegral . foldr lcm 1 . fmap (denominator . snd) $ allTerms
        transform = tseitinTransform *** (floor . (denominatorProduct *))
        transformedLeftHandSide = transform . first Not <$> leftHandTerms
        transformedRightHandSide = transform <$> rightHandTerms
        clauses = transformedLeftHandSide <> transformedRightHandSide
        k =   (fromIntegral . sum . fmap snd) transformedLeftHandSide
            + denominatorProduct * leftHandConstant
            + if strict then 0 else 1

instance ( Ord p
         , MonadPlus m
         , ConstrainedModelSearch d p m )
         => ModelSearch (NonEmpty d) (ProbabilityInequality p) m
  where
    findModel = findModel . summationNormalForm
