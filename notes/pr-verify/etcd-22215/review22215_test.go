package backend_test

import (
	"fmt"
	"sync"
	"testing"
	"time"

	"go.etcd.io/etcd/server/v3/storage/backend"
	betesting "go.etcd.io/etcd/server/v3/storage/backend/testing"
	"go.etcd.io/etcd/server/v3/storage/schema"
)

// Concurrent readers (shared and concurrent read txs, UnsafeRange and UnsafeForEach) racing
// with periodic commits and defrag; run with -race.
func TestReview22215ConcurrentReadersDefrag(t *testing.T) {
	b, _ := betesting.NewTmpBackend(t, time.Millisecond, 10)
	defer betesting.Close(t, b)
	tx := b.BatchTx()
	tx.Lock()
	tx.UnsafeCreateBucket(schema.Test)
	tx.Unlock()
	stop := make(chan struct{})
	var wg sync.WaitGroup
	for i := 0; i < 4; i++ {
		wg.Add(1)
		go func(i int) {
			defer wg.Done()
			for j := 0; ; j++ {
				select {
				case <-stop:
					return
				default:
				}
				tx := b.BatchTx()
				tx.Lock()
				tx.UnsafePut(schema.Test, []byte(fmt.Sprintf("k%d-%d", i, j%50)), []byte("v"))
				tx.Unlock()
			}
		}(i)
	}
	for i := 0; i < 4; i++ {
		wg.Add(1)
		go func(i int) {
			defer wg.Done()
			for {
				select {
				case <-stop:
					return
				default:
				}
				var rt backend.ReadTx
				if i%2 == 0 {
					rt = b.ConcurrentReadTx()
				} else {
					rt = b.ReadTx()
				}
				rt.RLock()
				rt.UnsafeRange(schema.Test, []byte("k"), []byte("l"), 1)
				rt.UnsafeRange(schema.Key, []byte("a"), []byte("z"), 0) // missing bucket
				_ = rt.UnsafeForEach(schema.Test, func(k, v []byte) error { return nil })
				_ = rt.UnsafeForEach(schema.Meta, func(k, v []byte) error { return nil })
				rt.RUnlock()
			}
		}(i)
	}
	for i := 0; i < 5; i++ {
		time.Sleep(50 * time.Millisecond)
		if err := b.Defrag(); err != nil {
			t.Fatal(err)
		}
	}
	close(stop)
	wg.Wait()
}
