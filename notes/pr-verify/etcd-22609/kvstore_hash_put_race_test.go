package mvcc

import (
	"sync"
	"testing"

	"go.uber.org/zap/zaptest"

	"go.etcd.io/etcd/server/v3/lease"
	betesting "go.etcd.io/etcd/server/v3/storage/backend/testing"
)

// TestHashConcurrentWithPut runs Hash while write transactions commit. Hash reads
// currentRev, which a write txn's End updates under revMu; the race detector
// reports it if Hash reads it without revMu.
func TestHashConcurrentWithPut(t *testing.T) {
	b, _ := betesting.NewDefaultTmpBackend(t)
	s := NewStore(zaptest.NewLogger(t), b, &lease.FakeLessor{}, StoreConfig{})
	defer cleanup(s, b)

	var wg sync.WaitGroup
	wg.Add(1)
	go func() {
		defer wg.Done()
		for i := 0; i < 10; i++ {
			if _, _, err := s.HashStorage().Hash(); err != nil {
				t.Error(err)
			}
		}
	}()
	for i := 0; i < 100; i++ {
		s.Put([]byte("foo"), []byte("bar"), lease.NoLease)
	}
	wg.Wait()
}
