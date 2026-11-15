package mvcc

import (
	"testing"

	"go.uber.org/zap/zaptest"

	"go.etcd.io/etcd/server/v3/lease"
	betesting "go.etcd.io/etcd/server/v3/storage/backend/testing"
)

// A restore to an older backend (a snapshot below the store's revision) with an unsynced watcher
// whose next revision is above the restored revision: the next sync panics (watcher_group.go's
// chooseAll), because Restore marks only the synced watchers `restore`.
func TestZZBackwardRestoreUnsyncedWatcher(t *testing.T) {
	bOld, _ := betesting.NewDefaultTmpBackend(t)
	old := NewStore(zaptest.NewLogger(t), bOld, &lease.FakeLessor{}, StoreConfig{})
	for i := 0; i < 2; i++ {
		old.Put([]byte("foo"), []byte("v"), lease.NoLease)
	}
	old.Commit() // revision 3 on disk

	b, _ := betesting.NewDefaultTmpBackend(t)
	s := newWatchableStore(zaptest.NewLogger(t), b, &lease.FakeLessor{}, StoreConfig{})
	for i := 0; i < 9; i++ {
		s.Put([]byte("foo"), []byte("v"), lease.NoLease)
	}
	// revision 10; a watcher catching up from revision 5 is unsynced
	w := s.NewWatchStream()
	defer w.Close()
	if _, err := w.Watch(t.Context(), 0, []byte("foo"), nil, 5); err != nil {
		t.Fatal(err)
	}
	if s.unsynced.size() != 1 {
		t.Fatalf("unsynced %d", s.unsynced.size())
	}
	if err := s.Restore(bOld); err != nil {
		t.Fatal(err)
	}
	t.Logf("restored: current revision %d", s.store.currentRev)
	defer func() {
		if r := recover(); r != nil {
			t.Fatalf("syncWatchers panicked after a backward restore: %v", r)
		}
	}()
	s.syncWatchers()
}
