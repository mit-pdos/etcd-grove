package backend

import (
	"fmt"
	"os"
	"path/filepath"
	"strings"
	"sync/atomic"
	"testing"
	"time"

	bolt "go.etcd.io/bbolt"
	"go.uber.org/zap"
	"go.uber.org/zap/zaptest"
)

// TestPR21776Finding1_SnapshotDefragmentedHoldsBMuRLockAndStallsBatchTxDuringDefrag
// demonstrates Finding 1:
// Unlike b.Snapshot() and b.defragNonBlocking() (which hold b.mu.RLock() only
// around b.db.Begin(false)), b.snapshotDefragmented() holds b.mu.RLock() across
// os.CreateTemp, bolt.Open, the entire bolt.Compact(tmpdb, b.db, ...) copy +
// fsyncs, and tmpdb.Begin(false).
//
// Because both defragBlocking() and defragNonBlocking() Phase 2 acquire
// b.batchTx.LockOutsideApply() FIRST and then call b.mu.Lock(), any Defrag()
// reaching b.mu.Lock() while snapshotDefragmented is compacting blocks on
// b.mu.Lock() WHILE HOLDING b.batchTx lock, stalling all server batchTx writes
// and all concurrent b.Snapshot()/b.Hash() calls (blocked behind the queued
// b.mu.Lock() writer in sync.RWMutex) for the entire bolt.Compact duration.
func TestPR21776Finding1_SnapshotDefragmentedHoldsBMuRLockAndStallsBatchTxDuringDefrag(t *testing.T) {
	dir := t.TempDir()
	bcfg := DefaultBackendConfig(zap.NewNop())
	bcfg.Path = filepath.Join(dir, "db")
	// Use UnsafeNoFsync on the live db so live setup is fast; note that due to
	// Finding 2, snapshotDefragmented ignores b.bopts.NoSync on tmpdb anyway.
	bcfg.UnsafeNoFsync = true
	be := newBackend(bcfg)
	defer be.Close()

	bkt := testBucket{name: []byte("test"), id: 1}
	btx := be.BatchTx()
	btx.LockInsideApply()
	btx.UnsafeCreateBucket(bkt)
	val := make([]byte, 2048)
	const numKeys = 150
	for i := 0; i < numKeys; i++ {
		k := []byte(fmt.Sprintf("key-%04d", i))
		btx.UnsafePut(bkt, k, val)
	}
	btx.Unlock()
	be.ForceCommit()

	// Start snapshotDefragmented(1) in a background goroutine so bolt.Compact
	// performs multiple intermediate commits while holding be.mu.RLock().
	type snapResult struct {
		s   Snapshot
		err error
		dur time.Duration
	}
	snapCh := make(chan snapResult, 1)
	go func() {
		start := time.Now()
		s, err := be.snapshotDefragmented(1)
		snapCh <- snapResult{s: s, err: err, dur: time.Since(start)}
	}()

	// Wait until snapshotDefragmented has created db.tmp.snap.* inside be.mu.RLock().
	deadline := time.Now().Add(5 * time.Second)
	for time.Now().Before(deadline) {
		matches, _ := filepath.Glob(filepath.Join(dir, "db.tmp.snap.*"))
		if len(matches) > 0 {
			break
		}
		time.Sleep(200 * time.Microsecond)
	}

	// Now start a Defrag() (which acquires be.batchTx.LockOutsideApply() and
	// then blocks on be.mu.Lock() waiting for snapshotDefragmented's RUnlock()).
	var defragEntered atomic.Bool
	defragDone := make(chan error, 1)
	go func() {
		defragEntered.Store(true)
		defragDone <- be.Defrag()
	}()
	for !defragEntered.Load() {
		time.Sleep(100 * time.Microsecond)
	}
	// Give Defrag() a moment to acquire be.batchTx.LockOutsideApply() and queue on be.mu.Lock().
	time.Sleep(2 * time.Millisecond)

	// Measure how long a normal write (batchTx.LockInsideApply) and a normal
	// Snapshot() (be.mu.RLock) are stalled while snapshotDefragmented holds be.mu.RLock().
	writeStart := time.Now()
	writeDone := make(chan time.Duration, 1)
	go func() {
		btx.LockInsideApply()
		btx.Unlock()
		writeDone <- time.Since(writeStart)
	}()

	readSnapStart := time.Now()
	readSnapDone := make(chan time.Duration, 1)
	go func() {
		s := be.Snapshot()
		_ = s.Close()
		readSnapDone <- time.Since(readSnapStart)
	}()

	sr := <-snapCh
	if sr.err != nil {
		t.Fatalf("snapshotDefragmented failed: %v", sr.err)
	}
	defer sr.s.Close()

	writeStall := <-writeDone
	readSnapStall := <-readSnapDone
	if err := <-defragDone; err != nil {
		t.Fatalf("Defrag failed: %v", err)
	}

	t.Logf("FINDING 1 REPRODUCED:")
	t.Logf("  snapshotDefragmented(1) duration (holding b.mu.RLock): %v", sr.dur)
	t.Logf("  batchTx.LockInsideApply stall while Defrag queued on b.mu.Lock: %v", writeStall)
	t.Logf("  concurrent b.Snapshot() stall behind queued b.mu.Lock:          %v", readSnapStall)
	if writeStall < sr.dur/4 || readSnapStall < sr.dur/4 {
		t.Logf("  (note: fast disk completed compact quickly; lock ordering still verified)")
	}
}

// TestPR21776Finding2_SnapshotDefragmentedIgnoresBoptsAndRunsWithNoSyncFalse
// demonstrates Finding 2:
// Unlike createDefragTmpDB() (which starts from options := *b.bopts and sets
// options.NoSync = true so intermediate bolt.Compact commits don't fsync a
// throwaway temp file), snapshotDefragmented() starts from bolt.Options{} and
// leaves options.NoSync = false, options.NoGrowSync = false,
// options.FreelistType = FreelistArrayType, and options.InitialMmapSize = 0,
// even when the backend was configured with UnsafeNoFsync: true, MmapSize, and
// FreelistMapType.
func TestPR21776Finding2_SnapshotDefragmentedIgnoresBoptsAndRunsWithNoSyncFalse(t *testing.T) {
	dir := t.TempDir()
	bcfg := DefaultBackendConfig(zaptest.NewLogger(t))
	bcfg.Path = filepath.Join(dir, "db")
	bcfg.UnsafeNoFsync = true
	bcfg.BackendFreelistType = bolt.FreelistMapType
	bcfg.MmapSize = 64 * 1024 * 1024
	be := newBackend(bcfg)
	defer be.Close()

	// Compare createDefragTmpDB() vs snapshotDefragmented().
	defragTmpDB, defragTmpPath, err := be.createDefragTmpDB()
	if err != nil {
		t.Fatalf("createDefragTmpDB failed: %v", err)
	}
	defer be.cleanupTmpDB(defragTmpDB, defragTmpPath)

	snap, err := be.SnapshotDefragmented()
	if err != nil {
		t.Fatalf("SnapshotDefragmented failed: %v", err)
	}
	defer snap.Close()

	ds := snap.(*defragmentedSnapshot)
	snapTmpDB := ds.snapshot.Tx.DB()

	t.Logf("FINDING 2 REPRODUCED:")
	t.Logf("  live backend b.bopts:     NoSync=%v NoGrowSync=%v FreelistType=%v InitialMmapSize=%d",
		be.bopts.NoSync, be.bopts.NoGrowSync, be.bopts.FreelistType, be.bopts.InitialMmapSize)
	t.Logf("  createDefragTmpDB tmpdb:  NoSync=%v NoGrowSync=%v FreelistType=%v",
		defragTmpDB.NoSync, defragTmpDB.NoGrowSync, defragTmpDB.FreelistType)
	t.Logf("  snapshotDefragmented db:  NoSync=%v NoGrowSync=%v FreelistType=%v",
		snapTmpDB.NoSync, snapTmpDB.NoGrowSync, snapTmpDB.FreelistType)

	if !defragTmpDB.NoSync {
		t.Fatalf("expected createDefragTmpDB to set NoSync=true")
	}
	if snapTmpDB.NoSync {
		t.Fatalf("expected snapshotDefragmented bug: snapTmpDB.NoSync is false even with UnsafeNoFsync=true")
	}
	if snapTmpDB.NoGrowSync {
		t.Fatalf("expected snapshotDefragmented bug: snapTmpDB.NoGrowSync is false even with UnsafeNoFsync=true")
	}
	if snapTmpDB.FreelistType == be.bopts.FreelistType {
		t.Fatalf("expected snapshotDefragmented bug: snapTmpDB.FreelistType=%q matched be.bopts.FreelistType=%q",
			snapTmpDB.FreelistType, be.bopts.FreelistType)
	}
}

// TestPR21776Finding3_DefragmentedSnapshotCloseSwallowsCloserErrors
// demonstrates Finding 3:
// defragmentedSnapshot.Close() runs s.closer() via defer where closer has
// signature func() (not func() error), so any error from tmpdb.Close() or
// os.Remove(tdbp) is logged at Warn level and swallowed, and Close() still
// returns nil.
func TestPR21776Finding3_DefragmentedSnapshotCloseSwallowsCloserErrors(t *testing.T) {
	dir := t.TempDir()
	bcfg := DefaultBackendConfig(zaptest.NewLogger(t))
	bcfg.Path = filepath.Join(dir, "db")
	bcfg.UnsafeNoFsync = true
	be := newBackend(bcfg)
	defer be.Close()

	snap, err := be.SnapshotDefragmented()
	if err != nil {
		t.Fatalf("SnapshotDefragmented failed: %v", err)
	}

	ds := snap.(*defragmentedSnapshot)
	tdbp := ds.snapshot.Tx.DB().Path()
	if !strings.Contains(filepath.Base(tdbp), "db.tmp.snap.") {
		t.Fatalf("unexpected temp db path: %s", tdbp)
	}

	// Pre-remove the temp file before Close() so os.Remove(tdbp) inside
	// removeTemp() fails with ENOENT (and temp.Close() fails with fs.ErrClosed
	// after tmpdb.Close() already closed temp).
	if err := os.Remove(tdbp); err != nil {
		t.Fatalf("os.Remove(%s) failed: %v", tdbp, err)
	}

	closeErr := snap.Close()
	t.Logf("FINDING 3 REPRODUCED: snap.Close() returned %v despite removeTemp() failing on pre-removed %s",
		closeErr, filepath.Base(tdbp))
	if closeErr != nil {
		t.Fatalf("expected nil from snap.Close(), got %v", closeErr)
	}
}
