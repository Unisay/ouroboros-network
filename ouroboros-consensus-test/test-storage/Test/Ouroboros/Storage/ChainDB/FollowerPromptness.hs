{-# LANGUAGE BlockArguments      #-}
{-# LANGUAGE DerivingStrategies  #-}
{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE NamedFieldPuns      #-}
{-# LANGUAGE RecordWildCards     #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections       #-}
{-# LANGUAGE ViewPatterns        #-}

-- | In the context of diffusion pipelining, it is important that (tentative)
-- followers promptly emit an instruction to roll forward after the tentative
-- header got set. We ensure this behavior by comparing the timestamps when a
-- tentative header got set and when a tentative follower emits an instruction
-- containing it.
module Test.Ouroboros.Storage.ChainDB.FollowerPromptness (tests) where

import           Control.Monad (forever)
import           Control.Monad.IOSim (runSimOrThrow)
import           Control.Tracer (Tracer (..), contramapM, nullTracer, traceWith)
import           Data.Foldable (for_)
import           Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import           Data.Set (Set)
import qualified Data.Set as Set

import           Test.QuickCheck
import           Test.Tasty
import           Test.Tasty.QuickCheck

import qualified Ouroboros.Network.MockChain.Chain as Chain

import           Ouroboros.Consensus.Block
import           Ouroboros.Consensus.Config
import           Ouroboros.Consensus.Fragment.InFuture
                     (CheckInFuture (CheckInFuture))
import           Ouroboros.Consensus.Fragment.Validated
                     (ValidatedFragment (validatedFragment))
import           Ouroboros.Consensus.HardFork.History.EraParams
                     (EraParams (eraEpochSize))
import           Ouroboros.Consensus.Storage.ChainDB.API (ChainDB)
import qualified Ouroboros.Consensus.Storage.ChainDB.API as ChainDB
import qualified Ouroboros.Consensus.Storage.ChainDB.API.Types.InvalidBlockPunishment as Punishment
import           Ouroboros.Consensus.Storage.ChainDB.Impl (ChainDbArgs (..))
import qualified Ouroboros.Consensus.Storage.ChainDB.Impl as ChainDBImpl
import           Ouroboros.Consensus.Storage.FS.API (SomeHasFS (SomeHasFS))
import qualified Ouroboros.Consensus.Storage.ImmutableDB as ImmutableDB
import           Ouroboros.Consensus.Storage.LedgerDB.DiskPolicy
                     (SnapshotInterval (DefaultSnapshotInterval),
                     defaultDiskPolicy)
import qualified Ouroboros.Consensus.Storage.VolatileDB as VolatileDB
import           Ouroboros.Consensus.Util.Condense (Condense (..))
import           Ouroboros.Consensus.Util.Enclose
import           Ouroboros.Consensus.Util.IOLike
import           Ouroboros.Consensus.Util.ResourceRegistry

import           Test.Util.ChainUpdates
import qualified Test.Util.FS.Sim.MockFS as MockFS
import           Test.Util.FS.Sim.STM (simHasFS)
import           Test.Util.Orphans.IOLike ()
import           Test.Util.TestBlock
import           Test.Util.Tracer (recordingTracerTVar)

tests :: TestTree
tests = testGroup "FollowerPromptness"
    [ testProperty "followerPromptness" prop_followerPromptness
    ]

prop_followerPromptness :: FollowerPromptnessTestSetup -> Property
prop_followerPromptness fpts =
    counterexample ("Trace:\n" <> unlines (ppTrace <$> traceByTime)) $
    counterexample (condense fpts) $
    counterexample ("Instruction timings: " <> condense followerInstrTimings) $
    counterexample ("Failed to pipeline: " <> condense notPipelined)
    (null notPipelined) .&&.
    counterexample ("Not processed: " <> condense unprocessed)
    (null unprocessed)
  where
    FollowerPromptnessOutcome{..} =
      runSimOrThrow $ runFollowerPromptnessTest fpts

    -- Hashes of tentative headers which were not immediately emitted as a
    -- follower instruction.
    notPipelined =
        tentativeHeadersWithoutFollowUp
          0
          followerInstrTimings

    -- Hashes of tentative header which were not processed (i.e. made obsolete
    -- due to adoption, or identified as a trap).
    unprocessed =
        tentativeHeadersWithoutFollowUp
          artificialDelay
          tentativeHeaderUnsetTimings

    -- Given a collection of timestamped hashes (considered as follow-up events
    -- of a specific hash), return the timestamped tentative header hashes which
    -- are not contained therein after the given delay.
    tentativeHeadersWithoutFollowUp ::
         DiffTime
      -> Map Time (Set TestHash)
      -> [(Time, Set TestHash)]
    tentativeHeadersWithoutFollowUp delay followUpTimings =
        [ (time, notFollowedUp)
        | (time, tentativeHashes) <- Map.toAscList tentativeHeaderSetTimings
        , let followUpHashes =
                Map.findWithDefault mempty (addTime delay time) followUpTimings
              notFollowedUp = tentativeHashes Set.\\ followUpHashes
        , not $ Set.null notFollowedUp
        ]

    ppTrace (time, ev) = show time <> ": " <> ev

data FollowerPromptnessOutcome = FollowerPromptnessOutcome {
    -- | The set of tentative headers by timestamp when set. With the current
    -- implementation of ChainSel, all sets should contain exactly one element.
    tentativeHeaderSetTimings   :: Map Time (Set TestHash)
  , -- | The set of tentative headers by timestamp when set.
    tentativeHeaderUnsetTimings :: Map Time (Set TestHash)
  , -- | The set of AddBlock instructions by a tentative follower by timestamp.
    followerInstrTimings        :: Map Time (Set TestHash)
  , traceByTime                 :: [(Time, String)]
  }

runFollowerPromptnessTest ::
     forall m. IOLike m
  => FollowerPromptnessTestSetup
  -> m FollowerPromptnessOutcome
runFollowerPromptnessTest FollowerPromptnessTestSetup{..} = withRegistry \registry -> do
    varTentativeSetTimings   <- uncheckedNewTVarM Map.empty
    varTentativeUnsetTimings <- uncheckedNewTVarM Map.empty
    varFollowerInstrTimings  <- uncheckedNewTVarM Map.empty

    (withTime -> tracer, getTrace) <- recordingTracerTVar

    let chainDBTracer = Tracer \case
            ChainDBImpl.TraceAddBlockEvent ev -> do
              traceWith tracer $ "ChainDB: " <> show ev
              case ev of
                ChainDBImpl.PipeliningEvent pev -> case pev of
                  ChainDBImpl.SetTentativeHeader hdr FallingEdge -> do
                    addTiming varTentativeSetTimings (headerHash hdr)
                    -- Wait 1s to delay the further chain selection logic (i.e.
                    -- simulating expensive block body validation).
                    threadDelay artificialDelay
                  ChainDBImpl.OutdatedTentativeHeader hdr ->
                    addTiming varTentativeUnsetTimings (headerHash hdr)
                  ChainDBImpl.TrapTentativeHeader hdr ->
                    addTiming varTentativeUnsetTimings (headerHash hdr)
                  _ -> pure ()
                _ -> pure ()
            _ -> pure ()
    chainDB <- openChainDB registry chainDBTracer

    -- Continually fetch instructions from a tentative follower.
    follower <-
      ChainDB.newFollower chainDB registry ChainDB.TentativeChain ChainDB.GetHash
    _ <- forkLinkedThread registry "Follower listener" $ forever $
      ChainDB.followerInstructionBlocking follower >>= \case
       Chain.AddBlock hdrHash -> addTiming varFollowerInstrTimings hdrHash
       Chain.RollBack _       -> pure ()

    -- Add all blocks to the ChainDB.
    let addBlock = ChainDB.addBlock_ chainDB Punishment.noPunishment
    for_ chainUpdates \case
      AddBlock blk      -> addBlock blk
      SwitchFork _ blks -> for_ blks addBlock

    tentativeHeaderSetTimings   <- readTVarIO varTentativeSetTimings
    tentativeHeaderUnsetTimings <- readTVarIO varTentativeUnsetTimings
    followerInstrTimings        <- readTVarIO varFollowerInstrTimings
    traceByTime                 <- getTrace
    pure FollowerPromptnessOutcome {..}
  where
    openChainDB ::
         ResourceRegistry m
      -> Tracer m (ChainDBImpl.TraceEvent TestBlock)
      -> m (ChainDB m TestBlock)
    openChainDB registry cdbTracer = do
        chainDbArgs <- do
          cdbHasFSImmutableDB <- mockedHasFS
          cdbHasFSVolatileDB  <- mockedHasFS
          cdbHasFSLgrDB       <- mockedHasFS
          let cdbImmutableDbValidation  = ImmutableDB.ValidateAllChunks
              cdbVolatileDbValidation   = VolatileDB.ValidateAll
              cdbMaxBlocksPerFile       = VolatileDB.mkBlocksPerFile 4
              cdbDiskPolicy             =
                defaultDiskPolicy securityParam DefaultSnapshotInterval
              cdbTopLevelConfig         = topLevelConfig
              cdbChunkInfo              = ImmutableDB.simpleChunkInfo epochSize
              cdbCheckIntegrity _blk    = True
              cdbGenesis                = pure testInitExtLedger
              cdbCheckInFuture          = CheckInFuture \vf ->
                                            pure (validatedFragment vf, [])
              cdbImmutableDbCacheConfig = ImmutableDB.CacheConfig 2 60
              cdbTraceLedger            = nullTracer
              cdbRegistry               = registry
              cdbBlocksToAddSize        = 1
              cdbGcDelay                = 1
              cdbGcInterval             = 1
          pure ChainDbArgs {..}
        (_, (chainDB, ChainDBImpl.Internal{intAddBlockRunner})) <-
          allocate
            registry
            (\_ -> ChainDBImpl.openDBInternal chainDbArgs False)
            (ChainDB.closeDB . fst)
        _ <- forkLinkedThread registry "AddBlockRunner" intAddBlockRunner
        pure chainDB
      where
        topLevelConfig = singleNodeTestConfigWithK securityParam
        epochSize      = eraEpochSize $ topLevelConfigLedger topLevelConfig

        mockedHasFS = SomeHasFS . simHasFS <$> newTVarIO MockFS.empty

    withTime = contramapM \ev -> (,ev) <$> getMonotonicTime

    addTiming varTiming hash = do
        now <- getMonotonicTime
        atomically $ modifyTVar varTiming $
          Map.alter (Just . maybe (Set.singleton hash) (Set.insert hash)) now

data FollowerPromptnessTestSetup = FollowerPromptnessTestSetup {
    chainUpdates :: [ChainUpdate]
  }
  deriving stock (Show)

instance Condense FollowerPromptnessTestSetup where
  condense FollowerPromptnessTestSetup{..} =
    "Chain updates: " <> condense chainUpdates

instance Arbitrary FollowerPromptnessTestSetup where
  arbitrary = do
      chainUpdates <- genChainUpdates TentativeChainBehavior securityParam 20
      pure FollowerPromptnessTestSetup {..}

  shrink FollowerPromptnessTestSetup{..} =
      [ FollowerPromptnessTestSetup {
            chainUpdates = init chainUpdates
          }
      | not $ null chainUpdates
      ]

securityParam :: SecurityParam
securityParam = SecurityParam 3

artificialDelay :: DiffTime
artificialDelay = 1
