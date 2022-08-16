{-# LANGUAGE DataKinds                  #-}
{-# LANGUAGE DeriveAnyClass             #-}
{-# LANGUAGE DeriveGeneric              #-}
{-# LANGUAGE DeriveTraversable          #-}
{-# LANGUAGE DerivingStrategies         #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE GeneralisedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase                 #-}
{-# LANGUAGE NamedFieldPuns             #-}
{-# LANGUAGE OverloadedStrings          #-}
{-# LANGUAGE RankNTypes                 #-}
{-# LANGUAGE RecordWildCards            #-}
{-# LANGUAGE ScopedTypeVariables        #-}
{-# LANGUAGE StandaloneDeriving         #-}
{-# LANGUAGE TypeApplications           #-}
{-# LANGUAGE TypeFamilies               #-}
{-# LANGUAGE TypeOperators              #-}
{-# LANGUAGE UndecidableInstances       #-}

{-# OPTIONS_GHC -Wno-orphans #-}
-- | FIXME: Remove
{-# OPTIONS_GHC -Wno-missing-methods #-}

module Test.Ouroboros.Storage.LedgerDB.HD.BackingStore (tests) where

import           Control.Monad
import qualified Control.Monad.Class.MonadSTM as STM
import           Control.Monad.Except hiding (lift)
import           Control.Monad.State hiding (lift)
import           Control.Tracer (nullTracer)
import           Data.Bifunctor
import           Data.Foldable (toList)
import           Data.Functor.Classes
import           Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import           Data.Maybe (fromJust)
import           GHC.Generics (Generic)
import qualified System.Directory as Dir
import           System.IO.Temp (createTempDirectory)

import           Test.QuickCheck (Gen)
import qualified Test.QuickCheck as QC
import qualified Test.QuickCheck.Monadic as QC
import           Test.StateMachine
import qualified Test.StateMachine.Types as QSM
import qualified Test.StateMachine.Types.Rank2 as Rank2
import           Test.Tasty (TestTree, testGroup)
import           Test.Tasty.QuickCheck (testProperty)

import           Ouroboros.Consensus.Block
import           Ouroboros.Consensus.Ledger.Abstract
import           Ouroboros.Consensus.Ledger.Basics ()
import           Ouroboros.Consensus.Storage.FS.API hiding (Handle)
import           Ouroboros.Consensus.Storage.FS.API.Types hiding (Handle)
import           Ouroboros.Consensus.Storage.FS.IO (ioHasFS)
import qualified Ouroboros.Consensus.Storage.LedgerDB.HD.BackingStore as BS
import           Ouroboros.Consensus.Storage.LedgerDB.OnDisk
import           Ouroboros.Consensus.Util.IOLike

import           Test.Util.Orphans.ToExpr ()



{------------------------------------------------------------------------------
  Top-level test tree
------------------------------------------------------------------------------}

tests :: TestTree
tests = testGroup "BackingStore" [
    testProperty "InMemory" $ prop_sequential InMemoryBackingStore
  ]

{------------------------------------------------------------------------------
  Mock of a @'BackingStore'@: Types
------------------------------------------------------------------------------}

data Mock values = Mock {
    backingValues    :: values
  , backingSeqNo     :: WithOrigin SlotNo
  , copies           :: [BS.BackingStorePath]
  , isClosed         :: Bool
  , openValueHandles :: Map MockHandle (MockValueReader values)
  , next             :: MockHandle
  }
  deriving stock (Show, Generic)

data MockValueReader values = MockValueReader {
    vhIsClosed :: Bool
  , values     :: values
  , seqNo      :: WithOrigin SlotNo
  }
  deriving stock (Show, Eq, Generic)

newtype MockHandle = MockHandle Int
  deriving stock (Show, Eq, Ord)
  deriving newtype Num

-- | An empty mock state.
emptyMock :: Operations keys values diff -> Mock values
emptyMock ops = Mock {
    backingValues     = emptyValues ops
  , backingSeqNo      = Origin
  , copies            = []
  , isClosed          = False
  , openValueHandles  = Map.empty
  , next              = 0
  }

data MockErr values =
    MockErrBackingStoreClosed
  | MockErrCopyPathAlreadyExists BS.BackingStorePath
  | MockErrNoMonotonicSeqNo (WithOrigin SlotNo) (WithOrigin SlotNo)
  | MockErrBSVHClosed MockHandle (Map MockHandle (MockValueReader values))
  | MockErrBSVHDoesNotExist MockHandle (Map MockHandle (MockValueReader values))
  deriving stock (Show, Eq)

-- | State within the mock runs.
newtype MockState values a =
    MockState (ExceptT (MockErr values) (State (Mock values)) a)
  deriving stock Functor
  deriving newtype ( Applicative, Monad
                   , MonadState (Mock values), MonadError (MockErr values)
                   )

runMockState ::
     MockState values a
  -> Mock values
  -> (Either (MockErr values) a, Mock values)
runMockState (MockState t) = runState (runExceptT t)

-- | Dictionary of functions on keys, values and diffs.
--
-- Since the mock is parameterised over keys, values and diffs, we must
-- pass in a dictionary of functions that defines how these types interact.
-- Example: @'applyDiff'@ defines how to apply a @diff@ to @values@.
data Operations keys values diff = Operations {
    applyDiff   :: diff -> values -> values
  , emptyValues :: values
  , takeValues  :: Int -> values -> values
  , splitValues:: keys -> values -> (values, values)
  , lookupKeys  :: keys -> values -> values
  }

{------------------------------------------------------------------------------
  Mock of a @'BackingStore'@: Mocked operations
------------------------------------------------------------------------------}

-- | Throw an error if the backing store has been closed, which prevents any
-- other operations from succeeding.
mGuardBSClosed :: MockState values ()
mGuardBSClosed = do
  closed <- gets isClosed
  when closed $
    throwError MockErrBackingStoreClosed

-- | Close the backing store.
mBSClose :: MockState values ()
mBSClose = do
  mGuardBSClosed
  modify (\m -> m {
      isClosed = True
    })

-- | Copy the contents of the backing store to the given path.
mBSCopy :: BS.BackingStorePath -> MockState values ()
mBSCopy bsp = do
  mGuardBSClosed
  cps <- gets copies
  when (bsp `elem` cps) $
    throwError $ MockErrCopyPathAlreadyExists bsp
  modify (\m -> m {
      copies = bsp : copies m
    })

-- | Open a new value handle, which captures the state of the backing store
-- at the time of opening the handle.
mBSValueHandle :: MockState values (WithOrigin SlotNo, MockHandle)
mBSValueHandle = do
  mGuardBSClosed
  vs <- gets backingValues
  seqNo <- gets backingSeqNo
  nxt <- gets next
  let
    vh = MockValueReader False vs seqNo
  modify (\m -> m {
      openValueHandles = Map.insert nxt vh (openValueHandles m)
    , next = nxt + 1
    })

  pure (seqNo, nxt)

-- | Write a diff to the backing store.
mBSWrite ::
     Operations keys values diff
  -> SlotNo
  -> diff
  -> MockState values ()
mBSWrite ops sl d = do
  mGuardBSClosed
  vs <- gets backingValues
  seqNo <- gets backingSeqNo
  when (seqNo > NotOrigin sl) $
    throwError $ MockErrNoMonotonicSeqNo seqNo (NotOrigin sl)
  modify (\m -> m {
      backingValues = applyDiff ops d vs
    , backingSeqNo = NotOrigin sl
    })

-- | Throw an error if the required backing store value handle has been closed.
mGuardBSVHClosed :: MockHandle -> MockState values (MockValueReader values)
mGuardBSVHClosed h = do
  vhs <- gets openValueHandles
  let vhMay = Map.lookup h vhs
  case vhIsClosed <$> vhMay of
    Nothing    -> throwError $ MockErrBSVHDoesNotExist h vhs
    Just False -> pure $ fromJust vhMay
    Just True  -> throwError $ MockErrBSVHClosed h vhs

-- | Close a backing store value handle.
mBSVHClose :: MockHandle -> MockState values ()
mBSVHClose h = do
  mGuardBSClosed
  void $ mGuardBSVHClosed h
  vhs <- gets openValueHandles
  modify (\m -> m {
    openValueHandles = Map.delete h vhs
  })

-- | Perform a range read on a backing store value handle.
mBSVHRangeRead ::
     Operations keys values diff
  -> MockHandle
  -> BS.RangeQuery keys
  -> MockState values values
mBSVHRangeRead ops h BS.RangeQuery{rqPrev, rqCount} = do
  mGuardBSClosed
  vh <- mGuardBSVHClosed h
  let
    vs = values vh
  case rqPrev of
    Nothing ->
      pure $ emptyValues ops
    Just ks ->
      pure $ takeValues ops rqCount $ snd $ splitValues ops ks vs

-- | Perform a regular read on a backing store value handle
mBSVHRead ::
     Operations keys values diff
  -> MockHandle
  -> keys
  -> MockState values values
mBSVHRead ops h ks = do
  mGuardBSClosed
  vh <- mGuardBSVHClosed h
  let vs = values vh
  pure $ lookupKeys ops ks vs

{------------------------------------------------------------------------------
  Reification of the API
------------------------------------------------------------------------------}

-- | Commands parameterised over the type of handle.
data Cmd keys values diff h =
    BSClose
  | BSCopy BS.BackingStorePath
  | BSValueHandle
  | BSWrite SlotNo diff
  | BSVHClose h
  | BSVHRangeRead h (BS.RangeQuery keys)
  | BSVHRead h keys
  deriving stock (Show, Functor, Foldable, Traversable)

-- | Successful results parameterised over the type of handle.
data Success keys values diff h =
    Unit ()
  | SHandle (WithOrigin SlotNo) h
  | Values values
  deriving stock (Show, Eq, Foldable, Functor, Traversable)

-- | Responses parameterised over the type of handle.
newtype Resp keys values diff h =
    Resp (Either (MockErr values) (Success keys values diff h))
  deriving stock (Show, Eq, Foldable, Functor, Traversable)

{------------------------------------------------------------------------------
  Interpreting the mock
------------------------------------------------------------------------------}

mAPI ::
     Operations keys values diff
  -> Cmd keys values diff MockHandle
  -> MockState values (Success keys values diff MockHandle)
mAPI ops = \case
  BSClose            -> Unit <$> mBSClose
  BSCopy bsp         -> Unit <$> mBSCopy bsp
  BSValueHandle      -> uncurry SHandle <$> mBSValueHandle
  BSWrite sl d       -> Unit <$> mBSWrite ops sl d
  BSVHClose h        -> Unit <$> mBSVHClose h
  BSVHRangeRead h rq -> Values <$> mBSVHRangeRead ops h rq
  BSVHRead h ks      -> Values <$> mBSVHRead ops h ks

runMock ::
     Operations keys values diff
  -> Cmd keys values diff MockHandle
  -> Mock values
  -> ( Resp keys values diff MockHandle
     , Mock values
     )
runMock ops cmd = first Resp . runMockState (mAPI ops cmd)

{------------------------------------------------------------------------------
  Interpreting implementations
------------------------------------------------------------------------------}

newtype Handle = Handle Int
  deriving stock (Show, Eq, Ord)
  deriving newtype Num

runImpl ::
     Monad m
  => SomeHasFS m
  -> BackingStoreWithHandleRegistry m keys values diff
  -> Cmd keys values diff Handle
  -> m (Resp keys values diff Handle)
runImpl sfhs bs cmd = case cmd of
    BSClose            -> mkUnit    <$> bsClose bs
    BSCopy bsp         -> mkUnit    <$> bsCopy bs sfhs bsp
    BSValueHandle      -> mkSHandle <$> bsValueHandle bs
    BSWrite sl d       -> mkUnit    <$> bsWrite bs sl d
    BSVHClose h        -> mkUnit    <$> bsvhClose bs h
    BSVHRangeRead h rq -> mkValues  <$> bsvhRangeRead bs h rq
    BSVHRead h ks      -> mkValues  <$> bsvhRead bs h ks
  where
    mkUnit    = Resp . Right . Unit
    mkSHandle = Resp . Right . uncurry SHandle
    mkValues  = Resp . Right . Values

data BackingStoreWithHandleRegistry m keys values diff = BackingStoreWithHandleRegistry {
    bsClose       :: !(m ())
  , bsCopy        :: !(SomeHasFS m -> BS.BackingStorePath -> m ())
  , bsValueHandle :: !(m (WithOrigin SlotNo, Handle))
  , bsWrite       :: !(SlotNo -> diff -> m ())
  , bsvhClose     :: !(Handle -> m ())
  , bsvhRangeRead :: !(Handle -> BS.RangeQuery keys -> m values)
  , bsvhRead      :: !(Handle -> keys -> m values)
  }

withHandleRegistry ::
     forall m. MonadSTM m
  => forall keys values diff . BS.BackingStore m keys values diff
  -> m (BackingStoreWithHandleRegistry m keys values diff)
withHandleRegistry bs = do
    ref <- STM.newTVarIO Map.empty
    let
      bs' = BackingStoreWithHandleRegistry {
          bsClose          = BS.bsClose bs
        , bsCopy           = BS.bsCopy bs
        , bsValueHandle  = BS.bsValueHandle bs
                             >>= mapM (registerHandle ref)
        , bsWrite          = BS.bsWrite bs
        , bsvhClose        = getHandle ref >=> BS.bsvhClose
        , bsvhRangeRead    = \h rq -> getHandle ref h >>= flip BS.bsvhRangeRead rq
        , bsvhRead         = \h ks -> getHandle ref h >>= flip BS.bsvhRead ks
        }
    pure bs'
  where
    registerHandle ::
         STM.TVar m (Map Handle (BS.BackingStoreValueHandle m keys values))
      -> BS.BackingStoreValueHandle m keys values
      -> m Handle
    registerHandle ref bsvh = STM.atomically $ do
      vhs <- STM.readTVar ref
      let
        h    = maybe 0 ((+1) . fst) (Map.lookupMax vhs)
        vhs' = Map.insert h bsvh vhs
      STM.writeTVar ref vhs'
      pure h

    getHandle ::
         STM.TVar m (Map Handle (BS.BackingStoreValueHandle m keys values))
      -> Handle
      -> m (BS.BackingStoreValueHandle m keys values)
    getHandle ref h = STM.atomically $ do
      vhs <- STM.readTVar ref
      pure $ vhs Map.! h

{------------------------------------------------------------------------------
  References
------------------------------------------------------------------------------}

{-
data Reference a r = Reference (r a)
data Symbolic a = Symbolic Var
data Concrete a = Concrete a
reference :: a -> Reference a Concrete
concrete  :: Reference a Concrete -> a
newtype Var = Var Int
-}

newtype At f r = At (f (Reference Handle r))
type    f :@ r = At f r

deriving instance Show (f (Reference Handle r)) => Show (At f r)

instance Functor f => Rank2.Functor (At f) where
  fmap = \f (At x) -> At $ fmap (lift f) x
    where
      lift :: (r x -> r' x) -> QSM.Reference x r -> QSM.Reference x r'
      lift f (QSM.Reference x) = QSM.Reference (f x)

instance Foldable f => Rank2.Foldable (At f) where
  foldMap = \f (At x) -> foldMap (lift f) x
    where
      lift :: (r x -> m) -> QSM.Reference x r -> m
      lift f (QSM.Reference x) = f x

instance Traversable t => Rank2.Traversable (At t) where
  traverse = \f (At x) -> At <$> traverse (lift f) x
    where
      lift :: Functor f
           => (r x -> f (r' x)) -> QSM.Reference x r -> f (QSM.Reference x r')
      lift f (QSM.Reference x) = QSM.Reference <$> f x

semantics ::
     IOLike m
  => SomeHasFS m
  -> BackingStoreWithHandleRegistry m keys values diff
  -> Cmd keys values diff :@ Concrete
  -> m (Resp keys values diff :@ Concrete)
semantics sfs bswhr (At c) = At . fmap reference <$>
  runImpl sfs bswhr (concrete <$> c)

{------------------------------------------------------------------------------
  Relating implementations
------------------------------------------------------------------------------}

type HandleRefs r = [(Reference Handle r, MockHandle)]

(!) :: Eq k => [(k, a)] -> k -> a
env ! r = fromJust (lookup r env)

data Model values r = Model (Mock values) (HandleRefs r)
  deriving stock Generic

deriving instance (Show (Mock values), Show1 r) => Show (Model values r)

initModel :: Operations keys values diff -> Model values r
initModel ops = Model (emptyMock ops) []

{------------------------------------------------------------------------------
  Stepping the model
------------------------------------------------------------------------------}

transition ::
     Eq1 r
  => Operations keys values diff
  -> Model values r
  -> Cmd keys values diff :@ r
  -> Resp keys values diff :@ r
  -> Model values r
transition ops m c = after . lockstep ops m c

toMock :: (Functor f, Eq1 r) => Model values r -> f :@ r -> f MockHandle
toMock (Model _ hs) (At fr) = (hs !) <$> fr

step ::
     Eq1 r
  => Operations keys values diff
  -> Model values r
  -> Cmd keys values diff :@ r
  -> (Resp keys values diff MockHandle, Mock values)
step ops m@(Model mock _) c = runMock ops (toMock m c) mock

data Event keys values diff r = Event {
    before   :: Model values r
  , cmd      :: Cmd keys values diff :@ r
  , after    :: Model values r
  , mockResp :: Resp keys values diff MockHandle
  }

lockstep ::
     Eq1 r
  => Operations keys values diff
  -> Model values r
  -> Cmd keys values diff :@ r
  -> Resp keys values diff :@ r
  -> Event keys values diff r
lockstep ops m@(Model _ hs) c (At resp) = Event {
      before = m
    , cmd = c
    , after = Model mock' (hs <> hs')
    , mockResp = resp'
    }
  where
    (resp', mock') = step ops m c
    hs' = zip (toList resp) (toList resp')

postcondition ::
     (Show values, Eq values)
  => Operations keys values diff
  -> Model values Concrete
  -> Cmd keys values diff :@ Concrete
  -> Resp keys values diff :@ Concrete
  -> Logic
postcondition ops m c r = toMock (after e) r .== mockResp e
  where
    e = lockstep ops m c r

{------------------------------------------------------------------------------
  Constructing symbolic responses
------------------------------------------------------------------------------}

symbolicResp ::
     Operations keys values diff
  -> Model values Symbolic
  -> Cmd keys values diff :@ Symbolic
  -> GenSym (Resp keys values diff :@ Symbolic)
symbolicResp ops m c = At <$> traverse (const genSym) resp
  where
    (resp, _mock') = step ops m c

{------------------------------------------------------------------------------
  Generating commands
------------------------------------------------------------------------------}

generator ::
     Model values Symbolic
  -> Maybe (Gen (Cmd keys values diff :@ Symbolic))
generator _ = Nothing

shrinker ::
     Model values Symbolic
  -> Cmd keys values diff :@ Symbolic
  -> [Cmd keys values diff :@ Symbolic]
shrinker _ _ = []

{------------------------------------------------------------------------------
  Putting it all together
------------------------------------------------------------------------------}

sm :: (Show values, Eq values)
  => Operations keys values diff
  -> SomeHasFS IO
  -> BackingStoreWithHandleRegistry IO keys values diff
  -> StateMachine
        (Model values)
        (At (Cmd keys values diff))
        IO
        (At (Resp keys values diff))
sm ops sfs bs = StateMachine {
      initModel     = initModel ops
    , transition    = transition ops
    , precondition  = precondition
    , postcondition = postcondition ops
    , invariant     = Nothing
    , generator     = generator
    , shrinker      = shrinker
    , semantics     = semantics sfs bs
    , mock          = symbolicResp ops
    , cleanup       = noCleanup
    }

precondition :: Model values Symbolic -> Cmd keys values diff :@ Symbolic -> Logic
precondition (Model _ hs) (At c) =
    forall (toList c) (`member` map fst hs)

{------------------------------------------------------------------------------
  Running the tests
------------------------------------------------------------------------------}

prop_sequential :: BackingStoreSelector IO -> QC.Property
prop_sequential bss =
    forAllCommands (sm ops sfs bs) Nothing $ \cmds ->
      QC.monadicIO $ do
        sfs' <- SomeHasFS . ioHasFS . MountPoint <$> do
          sysTmpDir <- QC.run Dir.getTemporaryDirectory
          QC.run $ createTempDirectory sysTmpDir "QSM"
        LedgerBackingStore bs' <- QC.run $
          newBackingStore @IO @(SimpleLedgerState Int Int) nullTracer bss sfs' polyEmptyLedgerTables
        bs'' <- QC.run $ withHandleRegistry bs'
        let sm' = sm ops sfs' bs''
        (hist, _model, res) <- runCommands sm' cmds
        prettyCommands sm' hist
          $ checkCommandNames cmds
          $ res QC.=== Ok
  where
    ops = Operations {
        applyDiff = undefined
      , emptyValues = undefined
      , takeValues = undefined
      , splitValues = undefined
      , lookupKeys = undefined
      }

    bs  = error "InMemoryBackingStore not used during command generation"
    sfs = error "SomeHasFS not used during command generation"

{------------------------------------------------------------------------------
  Aux
------------------------------------------------------------------------------}

instance CommandNames (At (Cmd keys values diff)) where
  cmdName (At BSClose{})       = "BSClose"
  cmdName (At BSCopy{})        = "BSCopy"
  cmdName (At BSValueHandle{}) = "BSValueHandle"
  cmdName (At BSWrite{})       = "BSWrite"
  cmdName (At BSVHClose{})     = "BSVHClose"
  cmdName (At BSVHRangeRead{}) = "BSVHRangeRead"
  cmdName (At BSVHRead{})      = "BSVHRead"

  cmdNames _ = [
      "BSClose"
    , "BSCopy"
    , "BSValueHandle"
    , "BSWrite"
    , "BSVHClose"
    , "BSVHRangeRead"
    , "BSVHRead"
    ]

deriving newtype instance ToExpr Handle
deriving newtype instance ToExpr MockHandle
deriving anyclass instance ToExpr values => ToExpr (MockValueReader values)
deriving anyclass instance ToExpr values => ToExpr (Mock values)
deriving anyclass instance (ToExpr (r Handle), ToExpr values) => ToExpr (Model values r)
deriving anyclass instance ToExpr FsPath
deriving newtype instance ToExpr BS.BackingStorePath
deriving newtype instance (ToExpr (LedgerTables (SimpleLedgerState Int Int) ValuesMK))

{-------------------------------------------------------------------------------
  Simple ledgers
-------------------------------------------------------------------------------}

-- Todo: Can we think of a more general datatype that can contain an
-- arbitrary number of states/tables, i.e., a number of tables that is not
-- fixed?
-- Todo: Should we compe up with unified test @'LedgerState'@s and
-- @'LedgerTables'@, like we are now doing for test blocks?
newtype SimpleLedgerState k v (mk :: MapKind) = SimpleLedgerState {
    lsSimple :: mk k v
  }

deriving instance (Eq (mk k v)) => Eq (SimpleLedgerState k v mk)
deriving instance (Eq (mk k v))
               => Eq (LedgerTables (SimpleLedgerState k v) mk)
deriving anyclass instance ShowLedgerState (SimpleLedgerState k v)
deriving anyclass instance ShowLedgerState (LedgerTables (SimpleLedgerState k v))
deriving instance (Show (mk k v))
               => Show (LedgerTables (SimpleLedgerState k v) mk)

instance (Ord k, Eq v)
      => TableStuff (SimpleLedgerState k v) where
  newtype LedgerTables (SimpleLedgerState k v) mk = SimpleLedgerTables {
    ltSimple :: mk k v
  } deriving Generic

  projectLedgerTables SimpleLedgerState{..} =
    SimpleLedgerTables lsSimple

  withLedgerTables st SimpleLedgerTables{..} =
    st { lsSimple = ltSimple }

  pureLedgerTables f =
    SimpleLedgerTables { ltSimple = f }

  mapLedgerTables f SimpleLedgerTables{ltSimple} =
    SimpleLedgerTables $ f ltSimple

  traverseLedgerTables f SimpleLedgerTables{ltSimple} =
    SimpleLedgerTables <$> f ltSimple

  zipLedgerTables f l r =
    SimpleLedgerTables (f (ltSimple l) (ltSimple r))

  zipLedgerTablesA f l r =
    SimpleLedgerTables <$> f (ltSimple l) (ltSimple r)

  zipLedgerTables2 f l m r =
    SimpleLedgerTables $ f (ltSimple l) (ltSimple m) (ltSimple r)

  zipLedgerTables2A f l c r =
    SimpleLedgerTables <$> f (ltSimple l) (ltSimple c) (ltSimple r)

  foldLedgerTables f SimpleLedgerTables{ltSimple} =
    f ltSimple

  foldLedgerTables2 f l r =
    f (ltSimple l) (ltSimple r)

  namesLedgerTables =
    SimpleLedgerTables { ltSimple = NameMK "ltSimple" }

deriving newtype instance NoThunks (mk k v)
               => NoThunks (LedgerTables (SimpleLedgerState k v) mk)
deriving anyclass instance SufficientSerializationForAnyBackingStore (SimpleLedgerState k v)
