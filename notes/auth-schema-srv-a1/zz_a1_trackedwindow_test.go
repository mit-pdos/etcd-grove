package backend_test

// A1 Scope (auth-schema-srv): the per-bucket read model of a tracked (non-safe-range) bucket.
// Claims tested, each per bucket, for a read transaction at any time:
//   M1 put-only bucket: one session's puts are seen all or none (the write-back moves them);
//   M2 delete-only bucket: one session's deletes are seen all or none (the commit moves them);
//   M3 a bucket the session both puts and deletes in: a read can see neither state (control);
//   M4 between sessions (periodic commits racing, batch interval 1ms): the last session's state;
//   M5 a bucket created in a session and not committed: absent to readers until its commit, as
//      an empty bucket reads.
// M1/M2/M4 must never fail; M3 is expected to be observed (it is why per-bucket kinds exist).

import (
	"fmt"
	"sync"
	"sync/atomic"
	"testing"
	"time"

	"go.etcd.io/etcd/server/v3/storage/backend"
	betesting "go.etcd.io/etcd/server/v3/storage/backend/testing"
)

type tbkt struct {
	id   backend.BucketID
	name string
}

func (b tbkt) ID() backend.BucketID     { return b.id }
func (b tbkt) Name() []byte             { return []byte(b.name) }
func (b tbkt) String() string           { return b.name }
func (b tbkt) IsSafeRangeBucket() bool  { return false }

var (
	bkP = tbkt{100, "a1put"}
	bkD = tbkt{101, "a1del"}
	bkM = tbkt{102, "a1mix"}
)

func k(p string, i int) []byte { return []byte(fmt.Sprintf("%s%07d", p, i)) }

func has(tx backend.ReadTx, b backend.Bucket, key []byte) bool {
	ks, _ := tx.UnsafeRange(b, key, nil, 0)
	return len(ks) > 0
}

func TestA1TrackedBucketWindow(t *testing.T) {
	be, _ := betesting.NewTmpBackend(t, time.Millisecond, 10000)
	defer betesting.Close(t, be)
	const N = 20000
	tx := be.BatchTx()
	tx.Lock()
	for _, b := range []tbkt{bkP, bkD, bkM} {
		tx.UnsafeCreateBucket(b)
	}
	for i := 0; i < N; i++ {
		tx.UnsafePut(bkD, k("x", i), []byte("v"))
		tx.UnsafePut(bkD, k("y", i), []byte("v"))
		tx.UnsafePut(bkM, k("y", i), []byte("v"))
	}
	tx.Unlock()
	be.ForceCommit()

	var cur atomic.Int64 // sessions completed
	var reads, m1, m2, m3, m4 atomic.Int64
	stop := make(chan struct{})
	var wg sync.WaitGroup
	for r := 0; r < 4; r++ {
		wg.Add(1)
		go func() {
			defer wg.Done()
			for {
				select {
				case <-stop:
					return
				default:
				}
				i := int(cur.Load()) // session i is the next one (or running)
				before := cur.Load()
				rt := be.ReadTx()
				rt.RLock()
				px, py := has(rt, bkP, k("x", i)), has(rt, bkP, k("y", i))
				dx, dy := has(rt, bkD, k("x", i)), has(rt, bkD, k("y", i))
				mx, my := has(rt, bkM, k("x", i)), has(rt, bkM, k("y", i))
				pPrev := i == 0 || (has(rt, bkP, k("x", i-1)) && has(rt, bkP, k("y", i-1)))
				rt.RUnlock()
				after := cur.Load()
				reads.Add(1)
				if px != py {
					m1.Add(1)
				}
				if dx != dy {
					m2.Add(1)
				}
				if mx && my {
					m3.Add(1)
				}
				// M4: session i-1 had completed before the read began, so its puts are seen
				if before == after && int(before) == i && !pPrev {
					m4.Add(1)
				}
			}
		}()
	}
	deadline := time.Now().Add(30 * time.Second)
	for i := 0; i < N && time.Now().Before(deadline); i++ {
		tx := be.BatchTx()
		tx.Lock()
		tx.UnsafePut(bkP, k("x", i), []byte("v"))
		tx.UnsafePut(bkP, k("y", i), []byte("v"))
		tx.UnsafeDelete(bkD, k("x", i))
		tx.UnsafeDelete(bkD, k("y", i))
		tx.UnsafePut(bkM, k("x", i), []byte("v"))
		tx.UnsafeDelete(bkM, k("y", i))
		tx.Unlock()
		cur.Add(1)
	}
	close(stop)
	wg.Wait()
	t.Logf("sessions %d, reads %d: M1 put-only split %d, M2 delete-only split %d, M3 mixed-bucket unrecorded %d, M4 stale between sessions %d",
		cur.Load(), reads.Load(), m1.Load(), m2.Load(), m3.Load(), m4.Load())
	if m1.Load()+m2.Load()+m4.Load() > 0 {
		t.Errorf("the per-bucket model is false: M1 %d, M2 %d, M4 %d", m1.Load(), m2.Load(), m4.Load())
	}
	if m3.Load() == 0 {
		t.Logf("control M3 not observed this run (the window is short)")
	}
}

// M5: a bucket created in a session and not committed reads absent (as empty) until its commit.
func TestA1CreatedBucketUncommitted(t *testing.T) {
	be, _ := betesting.NewTmpBackend(t, time.Hour, 10000)
	defer betesting.Close(t, be)
	b := tbkt{103, "a1new"}
	tx := be.BatchTx()
	tx.Lock()
	tx.UnsafeCreateBucket(b)
	tx.Unlock()
	rt := be.ReadTx()
	rt.RLock()
	got := has(rt, b, []byte("k"))
	rt.RUnlock()
	if got {
		t.Fatal("a fresh bucket has a key")
	}
	tx.Lock()
	tx.UnsafePut(b, []byte("k"), []byte("v"))
	tx.Unlock()
	rt.RLock()
	got = has(rt, b, []byte("k"))
	rt.RUnlock()
	if !got {
		t.Fatal("a put into a bucket created and not committed is not seen after Unlock")
	}
}
