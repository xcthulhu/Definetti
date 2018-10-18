module Main (main) where

import           Test.Tasty                              (defaultMain,
                                                          testGroup)

import           Logic.Tasty.Suite.LinearProgrammingTest (linearProgrammingTests)
import           Logic.Tasty.Suite.ProbabilityTest       (probabilityTests)
import           Logic.Tasty.Suite.PropositionalTest     (propositionalTests)
import           Logic.Tasty.Suite.TemporalTest          (temporalTests)


main :: IO ()
main = defaultMain $ testGroup "Definetti Tests"
                               [ propositionalTests
                               , probabilityTests
                               , temporalTests
                               , linearProgrammingTests
                               ]
