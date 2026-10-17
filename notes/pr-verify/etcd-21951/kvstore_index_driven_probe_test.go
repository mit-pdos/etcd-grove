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
	"fmt"
	"math/rand"
	"testing"
	"time"

	"github.com/stretchr/testify/require"
	"go.uber.org/zap/zaptest"

	"go.etcd.io/etcd/pkg/v3/traceutil"
	"go.etcd.io/etcd/server/v3/lease"
	"go.etcd.io/etcd/server/v3/storage/backend"
	betesting "go.etcd.io/etcd/server/v3/storage/backend/testing"
)

// TestProbeDefaultPathBuildsDeleteSet shows that with the feature gate off,
// treeIndex.Compact still builds the set of every revision to delete (and
// scheduleCompaction discards it): the default compaction now holds one map
// entry per deleted revision in memory, computed under the index lock.
func TestProbeDefaultPathBuildsDeleteSet(t *testing.T) {
	ti := newTreeIndex(zaptest.NewLogger(t))
	for i := int64(1); i <= 1000; i++ {
		ti.Put([]byte("foo"), Revision{Main: i})
	}
	keep, del := ti.Compact(1000)
	require.Len(t, keep, 1)
	require.Len(t, del, 999)
}

// TestProbeIndexDrivenStoresNoHash shows that with the gate on, a finished
// compaction stores no compaction hash, so the compaction-hash corruption
// check has nothing to compare.
func TestProbeIndexDrivenStoresNoHash(t *testing.T) {
	for _, gate := range []bool{false, true} {
		t.Run(fmt.Sprintf("gate=%v", gate), func(t *testing.T) {
			b, _ := betesting.NewDefaultTmpBackend(t)
			s := NewStore(zaptest.NewLogger(t), b, &lease.FakeLessor{}, StoreConfig{IndexDrivenCompaction: gate})
			defer cleanup(s, b)
			for i := 0; i < 5; i++ {
				s.Put([]byte("foo"), []byte(fmt.Sprint(i)), lease.NoLease)
			}
			ch, err := s.Compact(traceutil.TODO(), 4)
			require.NoError(t, err)
			<-ch
			if gate {
				require.Empty(t, s.HashStorage().Hashes())
			} else {
				require.Len(t, s.HashStorage().Hashes(), 1)
			}
		})
	}
}

// TestProbeDeletePutAtCompactRev: a transaction at revision c deletes a key and
// puts it again; compaction at c. The standard path deletes the put's row
// (etcd-io/etcd#22376), the index-driven path keeps it: the two modes leave
// different backends.
func TestProbeDeletePutAtCompactRev(t *testing.T) {
	ops := func(s *store) {
		s.Put([]byte("foo"), []byte("v1"), lease.NoLease) // rev 2
		txn := s.Write(traceutil.TODO())                  // rev 3
		txn.DeleteRange([]byte("foo"), nil)
		txn.Put([]byte("foo"), []byte("v2"), lease.NoLease)
		txn.End()
	}
	standard := compactKeyBucket(t, ops, 3, false)
	indexDriven := compactKeyBucket(t, ops, 3, true)
	t.Logf("standard: %d rows, index-driven: %d rows", len(standard), len(indexDriven))
	require.NotEqual(t, standard, indexDriven)
	require.Len(t, indexDriven, len(standard)+1)
}

type probeOp struct {
	del  bool
	key  string
	val  string
	more []probeOp // further changes of the same transaction
}

func randHistory(r *rand.Rand, n int, delPut bool) []probeOp {
	keys := []string{"a", "b", "c"}
	var ops []probeOp
	for i := 0; i < n; i++ {
		op := probeOp{del: r.Intn(3) == 0, key: keys[r.Intn(len(keys))], val: fmt.Sprint(i)}
		if delPut && op.del && r.Intn(2) == 0 {
			op.more = []probeOp{{key: op.key, val: fmt.Sprint(i) + "x"}}
		}
		ops = append(ops, op)
	}
	return ops
}

func applyHistory(s *store, ops []probeOp) {
	for _, op := range ops {
		txn := s.Write(traceutil.TODO())
		for _, o := range append([]probeOp{op}, op.more...) {
			if o.del {
				txn.DeleteRange([]byte(o.key), nil)
			} else {
				txn.Put([]byte(o.key), []byte(o.val), lease.NoLease)
			}
		}
		txn.End()
	}
}

// TestProbeIndexDrivenMatchesStandard: random histories over three keys (no
// delete-then-put in one revision), compacted at every revision, once or
// twice: both modes leave the same key bucket, and reads at or above the
// compaction revision answer as before compaction, also after re-opening.
func TestProbeIndexDrivenMatchesStandard(t *testing.T) {
	r := rand.New(rand.NewSource(1))
	for iter := 0; iter < 60; iter++ {
		ops := randHistory(r, 12, false)
		for c := int64(1); c <= 13; c++ {
			c2 := c + int64(r.Intn(3))
			t.Run(fmt.Sprintf("iter%d-c%d-c%d", iter, c, c2), func(t *testing.T) {
				apply := func(s *store) { applyHistory(s, ops) }
				run := func(gate bool) (map[string]string, map[int64]string) {
					b, tmp := betesting.NewDefaultTmpBackend(t)
					s := NewStore(zaptest.NewLogger(t), b, &lease.FakeLessor{}, StoreConfig{IndexDrivenCompaction: gate})
					apply(s)
					head := s.Rev()
					before := map[int64]string{}
					for rv := c2; rv <= head; rv++ {
						res, err := s.Range(t.Context(), []byte("a"), []byte("z"), RangeOptions{Rev: rv})
						require.NoError(t, err)
						before[rv] = fmt.Sprint(res.KVs)
					}
					for _, cc := range []int64{c, c2} {
						if cc > head {
							continue
						}
						ch, err := s.Compact(traceutil.TODO(), cc)
						if err != nil {
							continue
						}
						select {
						case <-ch:
						case <-time.After(10 * time.Second):
							t.Fatal("compaction timeout")
						}
					}
					bucket := readKeyBucket(t, b)
					s.Close()
					b.Close()
					b2 := backend.NewDefaultBackend(zaptest.NewLogger(t), tmp)
					s2 := NewStore(zaptest.NewLogger(t), b2, &lease.FakeLessor{}, StoreConfig{IndexDrivenCompaction: gate})
					defer cleanup(s2, b2)
					after := map[int64]string{}
					for rv := c2; rv <= head; rv++ {
						if rv > head {
							break
						}
						res, err := s2.Range(t.Context(), []byte("a"), []byte("z"), RangeOptions{Rev: rv})
						if err == nil {
							after[rv] = fmt.Sprint(res.KVs)
						}
					}
					for rv, v := range after {
						require.Equal(t, before[rv], v, "read at %d changed after compaction and reopen", rv)
					}
					return bucket, after
				}
				bs, _ := run(false)
				bi, _ := run(true)
				require.Equal(t, bs, bi, "iter %d c=%d c2=%d", iter, c, c2)
			})
		}
	}
}
