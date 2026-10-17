package etcdserver

import (
	"sync"
	"testing"

	"go.uber.org/zap/zaptest"

	betesting "go.etcd.io/etcd/server/v3/storage/backend/testing"
)

// Probes: backend readers under s.bemu that run after Cleanup closed the backend.
func newClosedBackendServer(t *testing.T) *EtcdServer {
	be, _ := betesting.NewDefaultTmpBackend(t)
	s := &EtcdServer{
		lgMu:     new(sync.RWMutex),
		lg:       zaptest.NewLogger(t),
		be:       be,
		stopping: make(chan struct{}, 1),
	}
	close(s.stopping)
	s.Cleanup()
	return s
}

func TestProbeStorageVersionAfterCleanup(t *testing.T) {
	s := newClosedBackendServer(t)
	defer func() {
		if r := recover(); r != nil {
			t.Fatalf("StorageVersion after Cleanup panicked: %v", r)
		}
	}()
	t.Logf("StorageVersion() = %v", s.StorageVersion())
}

func TestProbeDefragmentAfterCleanup(t *testing.T) {
	s := newClosedBackendServer(t)
	defer func() {
		if r := recover(); r != nil {
			t.Fatalf("Defragment after Cleanup panicked: %v", r)
		}
	}()
	t.Logf("Defragment() = %v", s.Defragment())
}

func TestProbeForceCommitAfterCleanup(t *testing.T) {
	s := newClosedBackendServer(t)
	defer func() {
		if r := recover(); r != nil {
			t.Fatalf("ForceCommit after Cleanup panicked: %v", r)
		}
	}()
	// what Compact does after a physical compaction (v3_server.go)
	s.bemu.RLock()
	s.be.ForceCommit()
	s.bemu.RUnlock()
	t.Log("ForceCommit returned")
}
