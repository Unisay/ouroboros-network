module Main (main) where

import           Test.Tasty

import qualified Ouroboros.Consensus.Util.Tests (tests)
import qualified Test.ThreadNet.Util.Tests (tests)
import qualified Test.Util.ChainUpdates.Tests (tests)
import qualified Test.Util.Schedule.Tests (tests)
import qualified Test.Util.Split.Tests (tests)

main :: IO ()
main = defaultMain tests

tests :: TestTree
tests =
  testGroup "test-infra"
  [ Ouroboros.Consensus.Util.Tests.tests
  , Test.ThreadNet.Util.Tests.tests
  , Test.Util.ChainUpdates.Tests.tests
  , Test.Util.Schedule.Tests.tests
  , Test.Util.Split.Tests.tests
  ]
