package etcdserver

import (
	"sync"
	"testing"

	"go.uber.org/zap/zaptest"

	betesting "go.etcd.io/etcd/server/v3/storage/backend/testing"
	"go.etcd.io/etcd/server/v3/storage/schema"
)

// Reviewer probe: maintenanceServer.Snapshot's first line,
// schema.ReadStorageVersion(ms.bg.Backend().ReadTx()), after Cleanup closed the backend.
// Backend() takes bemu but returns s.be; the read happens outside it, with no stopping check.
func TestProbeSnapshotReadStorageVersionAfterCleanup(t *testing.T) {
	be, _ := betesting.NewDefaultTmpBackend(t)
	s := &EtcdServer{
		lgMu:     new(sync.RWMutex),
		lg:       zaptest.NewLogger(t),
		be:       be,
		stopping: make(chan struct{}, 1),
	}
	close(s.stopping)
	s.Cleanup()
	defer func() {
		if r := recover(); r != nil {
			t.Fatalf("ReadStorageVersion(Backend().ReadTx()) after Cleanup panicked: %v", r)
		}
	}()
	t.Logf("ReadStorageVersion = %v", schema.ReadStorageVersion(s.Backend().ReadTx()))
}
