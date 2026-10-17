// Copyright 2026 The etcd Authors
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

package mvcc

import (
	"context"
	"fmt"
	"sync"
	"testing"

	"github.com/prometheus/client_golang/prometheus/testutil"
	"go.uber.org/zap/zaptest"

	"go.etcd.io/etcd/pkg/v3/traceutil"
	"go.etcd.io/etcd/server/v3/lease"
	betesting "go.etcd.io/etcd/server/v3/storage/backend/testing"
)

func reviewPayload(t *testing.T, kv KV) int64 {
	t.Helper()
	r, err := kv.Range(context.Background(), []byte{0}, []byte{0xff}, RangeOptions{})
	if err != nil {
		t.Fatal(err)
	}
	var n int64
	for _, item := range r.KVs {
		n += int64(len(item.Key) + len(item.Value))
	}
	return n
}

// TestReviewLogicalBytesMidTxn: the counter is updated per operation, inside the write
// transaction, before End publishes the revision. A lock-free reader (the gauge) sees
// (a) uncommitted changes that no read transaction can see yet, and (b) intermediate
// states of a transaction that deletes and re-puts a key with the same value.
func TestReviewLogicalBytesMidTxn(t *testing.T) {
	b, _ := betesting.NewDefaultTmpBackend(t)
	s := NewStore(zaptest.NewLogger(t), b, &lease.FakeLessor{}, StoreConfig{})
	defer cleanup(s, b)

	big := make([]byte, 1000)
	s.Put([]byte("k"), big, lease.NoLease)
	committed := reviewPayload(t, s)
	t.Logf("committed payload %d, LogicalBytes %d", committed, s.LogicalBytes())

	txn := s.Write(traceutil.TODO())
	txn.DeleteRange([]byte("k"), nil)
	mid := s.LogicalBytes()
	// a concurrent reader's view of the committed state while the txn is open
	var seen int64
	var wg sync.WaitGroup
	wg.Add(1)
	go func() { defer wg.Done(); seen = reviewPayload(t, s) }()
	wg.Wait()
	txn.Put([]byte("k"), big, lease.NoLease)
	txn.Put([]byte("new"), []byte("v"), lease.NoLease)
	pending := s.LogicalBytes()
	txn.End()
	after := s.LogicalBytes()
	t.Logf("mid-txn after delete: LogicalBytes %d while committed state (concurrent Range) has %d", mid, seen)
	t.Logf("mid-txn after re-put: LogicalBytes %d before End; after End %d (payload %d)", pending, after, reviewPayload(t, s))
	if mid == seen {
		t.Fatalf("expected a transient")
	}
}

// TestReviewLogicalBytesGlobalGauge: the Prometheus gauge is process-global and reports the
// last store whose metrics reporter was set up (NewStore), like the other db_* gauges.
func TestReviewLogicalBytesGlobalGauge(t *testing.T) {
	b1, _ := betesting.NewDefaultTmpBackend(t)
	s1 := NewStore(zaptest.NewLogger(t), b1, &lease.FakeLessor{}, StoreConfig{})
	defer cleanup(s1, b1)
	s1.Put([]byte("foo"), []byte("bar"), lease.NoLease)
	g1 := testutil.ToFloat64(dbLogicalSize)

	b2, _ := betesting.NewDefaultTmpBackend(t)
	s2 := NewStore(zaptest.NewLogger(t), b2, &lease.FakeLessor{}, StoreConfig{})
	defer cleanup(s2, b2)
	g2 := testutil.ToFloat64(dbLogicalSize)
	t.Logf("s1.LogicalBytes=%d s2.LogicalBytes=%d; gauge after s1=%v, after NewStore(s2)=%v",
		s1.LogicalBytes(), s2.LogicalBytes(), g1, g2)
}

// TestReviewLogicalBytesConcurrent: writers, compaction and snapshot Restore racing with
// lock-free readers of the gauge (run with -race); after quiescence the counter matches.
func TestReviewLogicalBytesConcurrent(t *testing.T) {
	oldChunk := restoreChunkKeys
	restoreChunkKeys = 3
	defer func() { restoreChunkKeys = oldChunk }()

	b, _ := betesting.NewDefaultTmpBackend(t)
	s := NewStore(zaptest.NewLogger(t), b, &lease.FakeLessor{}, StoreConfig{})
	defer cleanup(s, b)

	stop := make(chan struct{})
	var rd sync.WaitGroup
	for r := 0; r < 4; r++ {
		rd.Add(1)
		go func() {
			defer rd.Done()
			for {
				select {
				case <-stop:
					return
				default:
					_ = testutil.ToFloat64(dbLogicalSize)
					_ = s.LogicalBytes()
				}
			}
		}()
	}
	var wr sync.WaitGroup
	for w := 0; w < 4; w++ {
		wr.Add(1)
		go func(w int) {
			defer wr.Done()
			for i := 0; i < 200; i++ {
				k := []byte(fmt.Sprintf("k%d", (i*7+w)%23))
				switch i % 5 {
				case 0, 1, 2:
					s.Put(k, make([]byte, (i+w)%17), lease.NoLease)
				case 3:
					s.DeleteRange(k, nil)
				case 4:
					if rev := s.Rev(); rev > 2 {
						if ch, err := s.Compact(traceutil.TODO(), rev-1); err == nil {
							<-ch
						}
					}
				}
			}
		}(w)
	}
	wr.Wait()
	for i := 0; i < 3; i++ {
		s.Commit()
		if err := s.Restore(b); err != nil {
			t.Fatal(err)
		}
	}
	close(stop)
	rd.Wait()
	if got, want := s.LogicalBytes(), reviewPayload(t, s); got != want {
		t.Fatalf("LogicalBytes %d, payload %d", got, want)
	}
}
