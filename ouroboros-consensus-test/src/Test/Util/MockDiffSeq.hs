{-# LANGUAGE DeriveAnyClass             #-}
{-# LANGUAGE DeriveGeneric              #-}
{-# LANGUAGE DerivingVia                #-}
{-# LANGUAGE GeneralisedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase                 #-}
{-# LANGUAGE RankNTypes                 #-}
{-# LANGUAGE ScopedTypeVariables        #-}
{-# LANGUAGE StandaloneDeriving         #-}
{-# LANGUAGE StandaloneKindSignatures   #-}

module Test.Util.MockDiffSeq (
    -- * Types
    MockDiff (..)
  , MockDiffSeq (..)
  , MockKeys (..)
  , MockSlotNo (..)
  , MockValues (..)
    -- * Diff sequence operations
  , mFlush
  , mForwardValues
  , mForwardValuesAndKeys
  , mPush
  , mRollback
  , mTotalDiff
    -- * Utility functions
  , mDiffKeys
  , mFromListDeletes
  , mFromListInserts
  , mFromListKeys
  , mFromListValues
  , mLength
  , mRestrictValues
  ) where

import           Control.DeepSeq
import           Data.Bifunctor
import           Data.Foldable (fold)
import           Data.Kind
import qualified Data.Map.Merge.Strict as MapMerge
import           Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import           Data.Semigroup (Max (..))
import           Data.Sequence (Seq)
import qualified Data.Sequence as Seq
import           Data.Set (Set)
import qualified Data.Set as Set
import           GHC.Generics (Generic)



{------------------------------------------------------------------------------
  Types
------------------------------------------------------------------------------}

type MockDiffSeq :: Type -> Type -> Type
newtype MockDiffSeq k v = MockDiffSeq (Seq (MockSlotNo, MockDiff k v))
  deriving stock (Show, Generic)
  deriving anyclass NFData

-- | Simple diff datatype where @Nothing@ signals a delete, and @Just x@
-- signals an insert of @x@.
newtype MockDiff k v = MockDiff (Map k (Seq (Maybe v)))
  deriving stock (Show, Generic)
  deriving anyclass NFData

newtype MockValues k v = MockValues (Map k v)
  deriving stock (Show, Generic)
  deriving anyclass NFData

newtype MockKeys k v = MockKeys (Set k)
  deriving stock (Show, Generic)
  deriving anyclass NFData

newtype MockSlotNo = MockSlotNo Int
  deriving stock (Show, Eq, Ord, Generic)
  deriving newtype Num
  deriving anyclass NFData

{------------------------------------------------------------------------------
  Monoid instances
------------------------------------------------------------------------------}

instance Ord k => Semigroup (MockDiffSeq k v) where
  MockDiffSeq sq1 <> MockDiffSeq sq2 = MockDiffSeq $ sq1 <> sq2

instance Ord k => Monoid (MockDiffSeq k v) where
  mempty = MockDiffSeq mempty

deriving via Max Int instance Semigroup MockSlotNo
deriving via Max Int instance Monoid MockSlotNo

instance Ord k => Semigroup (MockDiff k v) where
  MockDiff d1 <> MockDiff d2 = MockDiff $
    MapMerge.merge
      MapMerge.preserveMissing
      MapMerge.preserveMissing
      (MapMerge.zipWithMatched (\_ x y -> x <> y))
      d1
      d2

instance Ord k => Monoid (MockDiff k v) where
  mempty = MockDiff mempty

{------------------------------------------------------------------------------
  Diff sequence operations
------------------------------------------------------------------------------}

-- | Push a diff to the right end of a diff sequence.
mPush ::
     MockDiffSeq k v
  -> MockSlotNo
  -> MockDiff k v
  -> MockDiffSeq k v
mPush (MockDiffSeq sq) sl d = MockDiffSeq $ case sq of
  Seq.Empty           -> Seq.singleton (sl, d)
  _ Seq.:|> (sl', _)
    | sl <= sl'       -> error "Slots should be monotonically increasing"
    | otherwise       -> sq Seq.:|> (sl, d)

-- | Flush @n@ diffs from a diff sequence by dropping @n@ diffs at the left end.
mFlush ::
     Int
  -> MockDiffSeq k v
  -> ( MockDiffSeq k v
     , MockDiffSeq k v
     )
mFlush n (MockDiffSeq sq) = bimap MockDiffSeq MockDiffSeq $
    Seq.splitAt n sq

-- | Roll back @n@ diffs in a diff sequence by dropping @n@ diffs at the right end.
mRollback ::
     Int
  -> MockDiffSeq k v
  -> ( MockDiffSeq k v
     , MockDiffSeq k v
     )
mRollback n (MockDiffSeq sq)
    | m < 0     =
        error "Can not roll back more than the length of a diff sequence"
    | otherwise = bimap MockDiffSeq MockDiffSeq $
        Seq.splitAt (Seq.length sq - n) sq
  where
    m = Seq.length sq - n

mForwardValuesAndKeys ::
     Ord k
  => MockValues k v
  -> MockKeys k v
  -> MockDiff k v
  -> MockValues k v
mForwardValuesAndKeys vs0@(MockValues vs) (MockKeys ks) (MockDiff d) =
    mForwardValues
      vs0
      (MockDiff $ d `Map.restrictKeys` (Map.keysSet vs `Set.union` ks))

mForwardValues ::
     Ord k
  => MockValues k v
  -> MockDiff k v
  -> MockValues k v
mForwardValues (MockValues m1) (MockDiff m2) = MockValues $
  MapMerge.merge
    MapMerge.preserveMissing
    (MapMerge.mapMaybeMissing (const lastSeq))
    (MapMerge.zipWithMaybeMatched (\_ _ -> lastSeq))
    m1
    m2
  where
    lastSeq = \case
      Seq.Empty   -> error "lastSeq: sequence is empty"
      _ Seq.:|> x -> x

mTotalDiff :: Ord k => MockDiffSeq k v -> MockDiff k v
mTotalDiff (MockDiffSeq sq) = snd $ fold sq

{------------------------------------------------------------------------------
  Utility functions
------------------------------------------------------------------------------}

mLength :: MockDiffSeq k v -> Int
mLength (MockDiffSeq sq) = Seq.length sq

mDiffKeys :: MockDiff k v -> MockKeys k v
mDiffKeys (MockDiff m) = MockKeys $ Map.keysSet m

mRestrictValues :: Ord k => MockValues k v -> MockKeys k v -> MockValues k v
mRestrictValues (MockValues m) (MockKeys s) = MockValues $ m `Map.restrictKeys` s

mSingletonDelete :: v -> Seq (Maybe v)
mSingletonDelete = Seq.singleton . const Nothing

mSingletonInsert :: v -> Seq (Maybe v)
mSingletonInsert = Seq.singleton . Just

mFromListDeletes :: Ord k => [(k, v)] -> MockDiff k v
mFromListDeletes = MockDiff . Map.fromList . fmap (second mSingletonDelete)

mFromListInserts :: Ord k => [(k, v)] -> MockDiff k v
mFromListInserts = MockDiff . Map.fromList . fmap (second mSingletonInsert)

mFromListKeys :: Ord k => [k] -> MockKeys k v
mFromListKeys = MockKeys . Set.fromList

mFromListValues :: Ord k => [(k, v)] -> MockValues k v
mFromListValues = MockValues . Map.fromList
