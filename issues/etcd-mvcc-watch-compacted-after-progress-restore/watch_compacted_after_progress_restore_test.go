package mvcc_test

import (
	"context"
	"fmt"
	"path/filepath"
	"testing"
	"time"

	"go.uber.org/zap"

	"go.etcd.io/etcd/pkg/v3/traceutil"
	"go.etcd.io/etcd/server/v3/lease"
	"go.etcd.io/etcd/server/v3/storage/backend"
	"go.etcd.io/etcd/server/v3/storage/mvcc"
)

// TestWatchCompactedAfterProgressRestore: a watcher told by a progress notification that nothing
// of it changed up to revision P is, after the store is restored from a later snapshot compacted at
// C <= P, sent a compaction response at C: its minRev never moved past its registration (a progress
// does not raise it).
func TestWatchCompactedAfterProgressRestore(t *testing.T) {
	lg := zap.NewNop()
	write := func(kv mvcc.KV, n int) {
		for i := 0; i < n; i++ {
			kv.Put([]byte(fmt.Sprintf("other%d", i)), []byte("v"), lease.NoLease)
		}
	}

	b1 := backend.NewDefaultBackend(lg, filepath.Join(t.TempDir(), "db1"))
	defer b1.Close()
	kv1 := mvcc.New(lg, b1, &lease.FakeLessor{}, mvcc.StoreConfig{})
	defer kv1.Close()

	ws := kv1.NewWatchStream()
	defer ws.Close()
	id, err := ws.Watch(context.TODO(), 0, []byte("w"), nil, 0) // registered at revision 1
	if err != nil {
		t.Fatal(err)
	}
	write(kv1, 20) // revisions 2..21, none of key "w"
	ws.RequestProgress(id)
	var p int64
	select {
	case resp := <-ws.Chan():
		if resp.WatchID != id || len(resp.Events) != 0 {
			t.Fatalf("expected a progress, got %+v", resp)
		}
		p = resp.Revision
	case <-time.After(time.Second):
		t.Fatal("no progress")
	}

	// A later snapshot of the same history (a member's applySnapshot), compacted at 10 <= p.
	b2 := backend.NewDefaultBackend(lg, filepath.Join(t.TempDir(), "db2"))
	defer b2.Close()
	kv2 := mvcc.NewStore(lg, b2, &lease.FakeLessor{}, mvcc.StoreConfig{})
	write(kv2, 25)
	done, err := kv2.Compact(traceutil.TODO(), 10)
	if err != nil {
		t.Fatal(err)
	}
	<-done
	kv2.Commit()
	kv2.Close()

	if err := kv1.Restore(b2); err != nil {
		t.Fatal(err)
	}
	select {
	case resp := <-ws.Chan():
		if resp.WatchID == id && resp.CompactRevision != 0 && resp.CompactRevision <= p {
			t.Fatalf("watcher told nothing changed up to %d is cancelled as compacted at %d", p, resp.CompactRevision)
		}
	case <-time.After(2 * time.Second):
	}
}
