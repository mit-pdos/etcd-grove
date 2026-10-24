// Copyright 2026 The etcd Authors
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

package mvcc

import (
	"fmt"
	"path/filepath"
	"runtime"
	"testing"
	"time"

	"go.uber.org/zap/zaptest"

	"go.etcd.io/etcd/pkg/v3/traceutil"
	"go.etcd.io/etcd/server/v3/lease"
	"go.etcd.io/etcd/server/v3/storage/backend"
	betesting "go.etcd.io/etcd/server/v3/storage/backend/testing"
	"go.etcd.io/etcd/server/v3/storage/schema"
)

// TestPR21397TombstoneKeyNeverDeleted demonstrates that PR #21397 never deletes
// tombstone keys (`<rev>t`, 18 bytes) from the bbolt `key` bucket during
// scheduleCompaction, because the producer goroutine strips the `'t'` suffix via
// BytesToRev(keys[i]) and the consumer reconstructs a 17-byte non-tombstone key
// via RevToBytes(rev, make([]byte, 8+1+8)) for tx.UnsafeDelete.
func TestPR21397TombstoneKeyNeverDeleted(t *testing.T) {
	b, _ := betesting.NewDefaultTmpBackend(t)
	s := NewStore(zaptest.NewLogger(t), b, &lease.FakeLessor{}, StoreConfig{})
	defer cleanup(s, b)

	// rev 2: put "foo" = "v1" (17-byte key in schema.Key)
	s.Put([]byte("foo"), []byte("v1"), lease.NoLease)
	// rev 3: delete "foo" (18-byte tombstone key in schema.Key ending with 't')
	s.DeleteRange([]byte("foo"), nil)
	// rev 4: put "foo" = "v2" (17-byte key in schema.Key)
	s.Put([]byte("foo"), []byte("v2"), lease.NoLease)

	// Flush readTx buffer so only bbolt is involved in this test.
	b.ForceCommit()

	// Compact at rev 4: only rev 4 is in `keep`; both rev 2 and rev 3 (tombstone)
	// must be deleted from schema.Key.
	done, err := s.Compact(traceutil.TODO(), 4)
	if err != nil {
		t.Fatalf("Compact failed: %v", err)
	}
	<-done

	tx := s.b.BatchTx()
	tx.Lock()
	keys, _ := tx.UnsafeRange(schema.Key, NewRevBytes(), []byte{0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff}, 0)
	tx.Unlock()

	var remaining []string
	var tombstoneStuck bool
	for _, k := range keys {
		rev := BytesToRev(k)
		tomb := isTombstone(k)
		remaining = append(remaining, fmt.Sprintf("rev=%d.%d(len=%d,tombstone=%v)", rev.Main, rev.Sub, len(k), tomb))
		if rev.Main == 3 && tomb {
			tombstoneStuck = true
		}
	}
	t.Logf("remaining keys in schema.Key after compact(4): %v", remaining)
	if tombstoneStuck {
		t.Fatalf("BUG (PR #21397): superseded tombstone key at rev 3 (18 bytes ending in 't') was NOT deleted by scheduleCompaction; remaining keys: %v", remaining)
	}
}

// TestPR21397ReadBufferSkipsCommittedKeysAndCorruptsHash demonstrates that
// switching scheduleCompaction from BatchTx.UnsafeRange to ReadTx.UnsafeRange
// with a batch limit skips committed bbolt keys and computes a wrong KeyValueHash
// whenever txReadBuffer holds uncommitted keys <= compactMainRev.
func TestPR21397ReadBufferSkipsCommittedKeysAndCorruptsHash(t *testing.T) {
	bcfg := backend.DefaultBackendConfig(zaptest.NewLogger(t))
	bcfg.Path = filepath.Join(t.TempDir(), "database")
	// Prevent periodic background commits during the test so we control exactly
	// which revisions are in bbolt vs txReadBuffer.
	bcfg.BatchInterval = time.Hour
	bcfg.BatchLimit = 10000
	b := backend.New(bcfg)
	defer b.Close()

	// CompactionBatchLimit = 5 so each UnsafeRange batch requests 5 keys.
	s := NewStore(zaptest.NewLogger(t), b, &lease.FakeLessor{}, StoreConfig{
		CompactionBatchLimit:    5,
		CompactionSleepInterval: time.Millisecond,
	})
	defer s.Close()

	// Write revisions 2..16 (15 revisions on the same key "k") and commit them to bbolt.
	for i := 2; i <= 16; i++ {
		s.Put([]byte("k"), []byte(fmt.Sprintf("val-%d", i)), lease.NoLease)
	}
	b.ForceCommit()

	// Write revisions 17 and 18 without ForceCommit: they sit in readTx.buf (txReadBuffer)
	// and bbolt's write tx, while readTx.tx (bbolt read tx) has revisions 2..16.
	s.Put([]byte("k"), []byte("val-17"), lease.NoLease)
	s.Put([]byte("k"), []byte("val-18"), lease.NoLease)

	// Reference hash at rev 18 before compaction (computed via HashByRev).
	wantHash, _, err := s.hashByRev(18)
	if err != nil {
		t.Fatalf("hashByRev(18) failed: %v", err)
	}

	// Run scheduleCompaction(18, 0):
	// First ReadTx.UnsafeRange(Key, 0, 19, 5) returns:
	//   3 keys from bbolt (revs 2, 3, 4) + 2 keys from readTx.buf (revs 17, 18).
	// The last key in the batch is rev 18, so `last` advances to {Main: 18, Sub: 1},
	// completely skipping committed bbolt keys at revisions 5..16!
	gotHash, err := s.scheduleCompaction(18, 0)
	if err != nil {
		t.Fatalf("scheduleCompaction(18, 0) failed: %v", err)
	}
	b.ForceCommit()

	// Check remaining keys in bbolt: only rev 18 should remain, but revs 5..16 were skipped!
	tx := s.b.BatchTx()
	tx.Lock()
	keys, _ := tx.UnsafeRange(schema.Key, NewRevBytes(), []byte{0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff}, 0)
	tx.Unlock()

	var remainingRevs []int64
	for _, k := range keys {
		remainingRevs = append(remainingRevs, BytesToRev(k).Main)
	}
	t.Logf("scheduleCompaction hash=%d, wantHash(hashByRev)=%d", gotHash.Hash, wantHash.Hash)
	t.Logf("remaining revisions in schema.Key after scheduleCompaction(18, 0): %v (want only [18])", remainingRevs)

	if gotHash.Hash != wantHash.Hash || len(remainingRevs) != 1 {
		t.Fatalf("BUG (PR #21397): ReadTx.UnsafeRange skipped committed bbolt revisions 5..16! gotHash=%d (want %d), remainingRevs=%v (want [18])",
			gotHash.Hash, wantHash.Hash, remainingRevs)
	}
}

// TestPR21397StopcGoroutineLeak demonstrates that when scheduleCompaction is
// interrupted by s.stopc, the producer goroutine is never stopped or waited for,
// blocking forever on `toDelRevsChan <- rev`.
func TestPR21397StopcGoroutineLeak(t *testing.T) {
	b, _ := betesting.NewDefaultTmpBackend(t)
	defer b.Close()

	// CompactionBatchLimit = 2 so toDelRevsChan has buffer capacity 2.
	s := NewStore(zaptest.NewLogger(t), b, &lease.FakeLessor{}, StoreConfig{
		CompactionBatchLimit:    2,
		CompactionSleepInterval: time.Hour,
	})

	// Write 10 revisions to "k"; compact at rev 11 deletes 9 revisions (revs 2..10).
	for i := 0; i < 10; i++ {
		s.Put([]byte("k"), []byte(fmt.Sprintf("v-%d", i)), lease.NoLease)
	}
	b.ForceCommit()

	beforeGoroutines := runtime.NumGoroutine()

	// Close stopc shortly after scheduleCompaction enters the sleep select after the first batch of 2 deletes.
	go func() {
		time.Sleep(50 * time.Millisecond)
		close(s.stopc)
	}()

	_, err := s.scheduleCompaction(11, 0)
	if err == nil {
		t.Fatalf("expected error from interrupted scheduleCompaction, got nil")
	}
	t.Logf("scheduleCompaction returned expected stop error: %v", err)

	// Give any exiting goroutine time to finish.
	time.Sleep(50 * time.Millisecond)
	afterGoroutines := runtime.NumGoroutine()
	t.Logf("goroutines before=%d, after=%d", beforeGoroutines, afterGoroutines)
	if afterGoroutines > beforeGoroutines {
		t.Fatalf("BUG (PR #21397): producer goroutine leaked after scheduleCompaction returned on <-s.stopc (goroutines before=%d, after=%d)",
			beforeGoroutines, afterGoroutines)
	}
}
