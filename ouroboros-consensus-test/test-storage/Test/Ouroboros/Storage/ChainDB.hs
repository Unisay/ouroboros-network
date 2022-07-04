module Test.Ouroboros.Storage.ChainDB (tests) where

import           Test.Tasty

import qualified Test.Ouroboros.Storage.ChainDB.FollowerPromptness as FollowerPromptness
import qualified Test.Ouroboros.Storage.ChainDB.GcSchedule as GcSchedule
import qualified Test.Ouroboros.Storage.ChainDB.Iterator as Iterator
import qualified Test.Ouroboros.Storage.ChainDB.Model.Test as Model
import qualified Test.Ouroboros.Storage.ChainDB.Paths as Paths
import qualified Test.Ouroboros.Storage.ChainDB.StateMachine as StateMachine

tests :: TestTree
tests = testGroup "ChainDB" [
      Iterator.tests
    , FollowerPromptness.tests
    , GcSchedule.tests
    , Model.tests
    , Paths.tests
    , StateMachine.tests
    ]
