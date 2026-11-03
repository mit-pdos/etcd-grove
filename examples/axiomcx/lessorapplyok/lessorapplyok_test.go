// Package lessorapplyok holds the Go checks of the axiom review of lessorApplyOk, the post of the
// lease.NewLessor axiom (notes/axiom-review/lessor-apply-ok.md). No counterexample: the review's
// verdict is "survives"; these tests check the Go facts its attacks ran into.
package lessorapplyok

import (
	"encoding/binary"
	"path/filepath"
	"testing"

	"github.com/Masterminds/semver/v3"
	"go.uber.org/zap"

	"go.etcd.io/etcd/server/v3/lease"
	"go.etcd.io/etcd/server/v3/storage/backend"
	"go.etcd.io/etcd/server/v3/storage/schema"
)

type cl struct{}

func (cl) Version() *semver.Version { return nil }

// TestOneLockPerWrite: with a post-lock hook set, every successful Grant and every persisting
// Checkpoint runs the hook exactly once (one LockInsideApply, so one Unlock: one write-back token
// per write), a rejected Grant none (it touches no backend); every record is in the Lease bucket
// as the readers see it after the Unlock.
func TestOneLockPerWrite(t *testing.T) {
	lg := zap.NewNop()
	be := backend.NewDefaultBackend(lg, filepath.Join(t.TempDir(), "db"))
	defer be.Close()
	hooks := 0
	be.SetTxPostLockInsideApplyHook(func() { hooks++ })
	le := lease.NewLessor(lg, be, cl{}, lease.LessorConfig{MinLeaseTTL: 1, CheckpointPersist: true})
	defer le.Stop()
	h0 := hooks
	const n = 2000
	for i := 1; i <= n; i++ {
		if _, err := le.Grant(lease.LeaseID(i), 600); err != nil {
			t.Fatal(err)
		}
	}
	if hooks-h0 != n {
		t.Fatalf("grants: %d hook runs, want %d", hooks-h0, n)
	}
	h1 := hooks
	for _, c := range []struct {
		id  lease.LeaseID
		ttl int64
	}{{0, 10}, {1, 10}, {5, lease.MaxLeaseTTL + 1}} {
		if _, err := le.Grant(c.id, c.ttl); err == nil {
			t.Fatalf("grant %v accepted", c)
		}
	}
	if hooks != h1 {
		t.Fatalf("rejected grants ran the hook %d times", hooks-h1)
	}
	for i := 1; i <= n; i++ {
		le.Checkpoint(lease.LeaseID(i), 7)
	}
	le.Checkpoint(lease.LeaseID(n+1), 7) // not granted: no write
	if hooks-h1 != n {
		t.Fatalf("checkpoints: %d hook runs, want %d", hooks-h1, n)
	}
	rt := be.ConcurrentReadTx()
	defer rt.RUnlock()
	k := make([]byte, 8)
	binary.BigEndian.PutUint64(k, n)
	ks, _ := rt.UnsafeRange(schema.Lease, k, nil, 0)
	if len(ks) != 1 {
		t.Fatalf("record %d not seen by a reader begun after the write", n)
	}
}

// TestZeroLoggerInfo (outside this review; a lead on the zap axioms, which quantify over every
// non-nil *zap.Logger): the zero Logger has a nil core, and Info panics.
func TestZeroLoggerInfo(t *testing.T) {
	defer func() {
		if r := recover(); r == nil {
			t.Fatal("no panic")
		} else {
			t.Logf("panic: %v", r)
		}
	}()
	(&zap.Logger{}).Info("x")
}
