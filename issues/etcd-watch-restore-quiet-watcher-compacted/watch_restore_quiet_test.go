// Reproduction of issues/etcd-watch-restore-quiet-watcher-compacted.md.
//
// Package mvcc, file server/storage/mvcc/watch_restore_quiet_test.go of go.etcd.io/etcd
// (module go.etcd.io/etcd/server/v3), at the etcd pin of etc/goose.py: 107edf7e4 (branch
// goose-lean of upamanyus/etcd; the same code as upstream main b25719d10).
//
// Run, in server/:
//
//	GOTOOLCHAIN=go1.27.1 go test ./storage/mvcc -run '^TestWatchRestoreQuietWatcherSpuriousCompaction$' -count=1
//
// Fails at the pin (shows the bug): "watcher of an untouched key canceled: CompactRevision=11, events=0".
package mvcc

import (
	"context"
	"testing"
	"time"

	"go.uber.org/zap/zaptest"

	"go.etcd.io/etcd/pkg/v3/traceutil"
	"go.etcd.io/etcd/server/v3/lease"
	betesting "go.etcd.io/etcd/server/v3/storage/backend/testing"
)

func TestWatchRestoreQuietWatcherSpuriousCompaction(t *testing.T) {
	b, _ := betesting.NewDefaultTmpBackend(t)
	s := New(zaptest.NewLogger(t), b, &lease.FakeLessor{}, StoreConfig{}).(*watchableStore)
	defer cleanup(s, b)

	w := s.NewWatchStream()
	defer w.Close()
	if _, err := w.Watch(context.TODO(), 0, []byte("quiet"), nil, 0); err != nil { // synced, minRev = 2
		t.Fatal(err)
	}
	var rev int64
	for i := 0; i < 10; i++ {
		rev = s.Put([]byte("busy"), []byte("v"), lease.NoLease)
	}
	done, err := s.Compact(traceutil.TODO(), rev)
	if err != nil {
		t.Fatal(err)
	}
	<-done
	if err := s.Restore(b); err != nil { // as on a snapshot install
		t.Fatal(err)
	}
	select {
	case resp := <-w.Chan():
		t.Fatalf("watcher of an untouched key canceled: CompactRevision=%d, events=%d", resp.CompactRevision, len(resp.Events))
	case <-time.After(3 * watchResyncPeriod):
	}
}
