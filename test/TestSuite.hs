import           Logic.PropositionalTest (test_hunitSimpleIdentities,
                                          test_qcPropositionalSemanticsLaws)
import           Test.Tasty              (defaultMain, testGroup)

main :: IO ()
main = defaultMain
  $ testGroup "Tests" [ test_hunitSimpleIdentities
                      , test_qcPropositionalSemanticsLaws]
