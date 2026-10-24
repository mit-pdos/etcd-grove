package lease

import (
	"context"
	"os"
	"sync/atomic"
	"testing"
	"time"

	"go.uber.org/zap"

	pb "go.etcd.io/etcd/api/v3/etcdserverpb"
	"go.etcd.io/etcd/server/v3/storage/schema"
)

// TestLessorRenewConcurrentCheckpointShortensExpiry demonstrates the remaining
// race in lessor.Renew (server/lease/lessor.go:412-455):
//
// Renew checks clearRemainingTTL := le.cp != nil && l.remainingTTL > 0 under
// le.mu.RLock(), releases le.mu.RUnlock() at line 414, optionally calls le.cp
// without holding le.mu at line 437, and then re-acquires le.mu.Lock() at line
// 442 and calls l.refresh(0) at line 449 without clearing l.remainingTTL.
//
// If a scheduled Checkpoint(id, r) (with 0 < r < l.ttl) applies between
// Renew's RUnlock (or after Renew's Checkpoint(id, 0) applies) and Renew's
// Lock at line 442:
//  1. Checkpoint sets l.remainingTTL = r (and persists RemainingTTL: r in bbolt).
//  2. Renew acquires le.mu.Lock() and calls l.refresh(0), which uses
//     l.getRemainingTTL() == r instead of l.ttl to set l.expiry = now + r.
//  3. Renew returns (l.ttl, nil) to the caller while the lease's actual expiry
//     is shortened to r seconds and l.remainingTTL remains r in memory and bbolt.
func TestLessorRenewConcurrentCheckpointShortensExpiry(t *testing.T) {
	const (
		leaseID       = LeaseID(1)
		nominalTTL    = int64(100)
		initialRemTTL = int64(20)
		staleRemTTL   = int64(5)
	)

	t.Run("ScheduledCheckpointAppliesDuringClear", func(t *testing.T) {
		lg := zap.NewNop()
		dir, be := NewTestBackend(t)
		defer os.RemoveAll(dir)
		defer be.Close()

		le := newLessor(lg, be, clusterLatest(), LessorConfig{
			MinLeaseTTL:       minLeaseTTL,
			CheckpointPersist: true,
		})
		defer le.Stop()

		l, err := le.Grant(leaseID, nominalTTL)
		if err != nil {
			t.Fatalf("Grant failed: %v", err)
		}
		if err := le.Checkpoint(leaseID, initialRemTTL); err != nil {
			t.Fatalf("initial Checkpoint failed: %v", err)
		}
		le.Promote(0)

		le.SetCheckpointer(func(ctx context.Context, cp *pb.LeaseCheckpointRequest) error {
			for _, c := range cp.Checkpoints {
				if err := le.Checkpoint(LeaseID(c.ID), c.Remaining_TTL); err != nil {
					return err
				}
			}
			// Simulate an already-proposed periodic Checkpoint(leaseID, staleRemTTL)
			// being applied on the Raft apply goroutine before Renew re-acquires le.mu.Lock().
			return le.Checkpoint(leaseID, staleRemTTL)
		})

		gotTTL, err := le.Renew(leaseID)
		if err != nil {
			t.Fatalf("Renew returned unexpected error: %v", err)
		}
		if gotTTL != nominalTTL {
			t.Fatalf("Renew returned ttl=%d, want %d", gotTTL, nominalTTL)
		}

		rem := l.Remaining()
		tx := be.ReadTx()
		tx.RLock()
		lpb := schema.MustUnsafeGetLease(tx, int64(leaseID))
		tx.RUnlock()

		t.Logf("after Renew: returned ttl=%ds, actual l.Remaining()=%v, in-memory l.remainingTTL=%d, persisted RemainingTTL=%d",
			gotTTL, rem, l.remainingTTL, lpb.RemainingTTL)

		if rem <= time.Duration(staleRemTTL)*time.Second {
			t.Fatalf("BUG: Renew returned ttl=%ds, nil, but l.Remaining()=%v (shortened to stale checkpoint TTL %ds; in-memory remainingTTL=%d, persisted RemainingTTL=%d)",
				gotTTL, rem, staleRemTTL, l.remainingTTL, lpb.RemainingTTL)
		}
	})

	t.Run("ScheduledCheckpointAppliesBetweenRUnlockAndLock", func(t *testing.T) {
		lg := zap.NewNop()
		dir, be := NewTestBackend(t)
		defer os.RemoveAll(dir)
		defer be.Close()

		le := newLessor(lg, be, clusterLatest(), LessorConfig{
			MinLeaseTTL:       minLeaseTTL,
			CheckpointPersist: true,
		})
		defer le.Stop()

		l, err := le.Grant(leaseID, nominalTTL)
		if err != nil {
			t.Fatalf("Grant failed: %v", err)
		}
		le.Promote(0)

		var cpCalls atomic.Int32
		le.SetCheckpointer(func(ctx context.Context, cp *pb.LeaseCheckpointRequest) error {
			cpCalls.Add(1)
			return nil
		})

		// Hold l.expiryMu.Lock() so that Renew:
		//  1. Acquires le.mu.RLock() (line 397), sees l.remainingTTL == 0
		//     (clearRemainingTTL == false at line 412), and releases le.mu.RUnlock()
		//     at line 414.
		//  2. Blocks on l.expiryMu.RLock() inside l.expired() -> l.Remaining() at
		//     line 415, right between le.mu.RUnlock() (line 414) and le.mu.Lock()
		//     (line 442).
		l.expiryMu.Lock()

		type renewResult struct {
			ttl int64
			err error
		}
		renewDone := make(chan renewResult, 1)
		go func() {
			ttl, rerr := le.Renew(leaseID)
			renewDone <- renewResult{ttl: ttl, err: rerr}
		}()

		// Wait until Renew has released le.mu.RUnlock() and is blocked at l.expired().
		time.Sleep(10 * time.Millisecond)

		// Apply a scheduled Checkpoint(leaseID, staleRemTTL) while Renew is paused
		// between le.mu.RUnlock() and le.mu.Lock().
		if err := le.Checkpoint(leaseID, staleRemTTL); err != nil {
			l.expiryMu.Unlock()
			t.Fatalf("Checkpoint failed: %v", err)
		}

		// Release l.expiryMu so Renew proceeds to le.mu.Lock() and calls l.refresh(0).
		l.expiryMu.Unlock()

		res := <-renewDone
		if res.err != nil {
			t.Fatalf("Renew returned unexpected error: %v", res.err)
		}
		if res.ttl != nominalTTL {
			t.Fatalf("Renew returned ttl=%d, want %d", res.ttl, nominalTTL)
		}

		rem := l.Remaining()
		tx := be.ReadTx()
		tx.RLock()
		lpb := schema.MustUnsafeGetLease(tx, int64(leaseID))
		tx.RUnlock()

		t.Logf("after Renew (cpCalls=%d): returned ttl=%ds, actual l.Remaining()=%v, in-memory l.remainingTTL=%d, persisted RemainingTTL=%d",
			cpCalls.Load(), res.ttl, rem, l.remainingTTL, lpb.RemainingTTL)

		if rem <= time.Duration(staleRemTTL)*time.Second {
			t.Fatalf("BUG: Renew returned ttl=%ds, nil (cpCalls=%d), but l.Remaining()=%v (shortened to stale checkpoint TTL %ds; in-memory remainingTTL=%d, persisted RemainingTTL=%d)",
				res.ttl, cpCalls.Load(), rem, staleRemTTL, l.remainingTTL, lpb.RemainingTTL)
		}
	})
}
