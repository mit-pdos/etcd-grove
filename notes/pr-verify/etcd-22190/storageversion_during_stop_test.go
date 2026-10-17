// The PR's regression test (etcd-io/etcd#22190 at 455bf3f8a, server/etcdserver/server_test.go),
// as a file of its own, to copy into server/etcdserver of a checkout.
package etcdserver

import (
	"sync"
	"testing"

	"github.com/stretchr/testify/assert"
	"go.uber.org/zap/zaptest"

	betesting "go.etcd.io/etcd/server/v3/storage/backend/testing"
)

func TestStorageVersionDuringStopCopy(t *testing.T) {
	newStoppingServer := func(t *testing.T) *EtcdServer {
		be, _ := betesting.NewDefaultTmpBackend(t)
		return &EtcdServer{
			lgMu:     new(sync.RWMutex),
			lg:       zaptest.NewLogger(t),
			be:       be,
			stopping: make(chan struct{}, 1),
		}
	}

	t.Run("AfterCleanup", func(t *testing.T) {
		s := newStoppingServer(t)
		close(s.stopping)
		s.Cleanup()
		assert.NotPanics(t, func() {
			assert.Nil(t, s.StorageVersion())
		})
	})

	t.Run("ConcurrentWithCleanup", func(t *testing.T) {
		s := newStoppingServer(t)
		var wg sync.WaitGroup
		for range 8 {
			wg.Add(1)
			go func() {
				defer wg.Done()
				defer func() {
					if r := recover(); r != nil {
						t.Errorf("StorageVersion panicked: %v", r)
					}
				}()
				for range 100 {
					s.StorageVersion()
				}
			}()
		}
		close(s.stopping)
		s.Cleanup()
		wg.Wait()
	})
}
