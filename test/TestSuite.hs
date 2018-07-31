module Main (main) where

import           Test.Tasty              (defaultMain, testGroup)

import           Logic.ProbabilityTest   (probabilityTests)
import           Logic.PropositionalTest (propositionalTests)
import           Logic.TemporalTest      (temporalTests)


main :: IO ()
main = defaultMain $ testGroup "Definetti Tests"
                               [ propositionalTests
                               , probabilityTests
                               , temporalTests
                               ]
