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
	mrand "math/rand"
	"testing"

	"go.uber.org/zap/zaptest"

	"go.etcd.io/etcd/api/v3/mvccpb"
	"go.etcd.io/etcd/pkg/v3/traceutil"
	"go.etcd.io/etcd/server/v3/lease"
	betesting "go.etcd.io/etcd/server/v3/storage/backend/testing"
)

// checkFastKeysOnly compares, at every revision from first to the store's current one, the
// fast keys-only range (read from the in-memory index) with the full range (read from the
// backend): the same keys, with the same revisions, versions and leases.
func checkFastKeysOnly(t *testing.T, s *store, first int64, phase string) {
	t.Helper()
	cur := s.Rev()
	for rev := first; rev <= cur; rev++ {
		for _, end := range [][]byte{nil, []byte("k\xff")} {
			for i := 0; i < 6 || end != nil; i++ {
				key := []byte(fmt.Sprintf("k%d", i))
				if end != nil {
					key = []byte("k")
				}
				full, err := s.Range(t.Context(), key, end, RangeOptions{Rev: rev})
				if err != nil {
					t.Fatalf("%s: full range at %d: %v", phase, rev, err)
				}
				fast, err := s.Range(t.Context(), key, end, RangeOptions{Rev: rev, FastKeysOnly: true})
				if err != nil {
					t.Fatalf("%s: fast range at %d: %v", phase, rev, err)
				}
				if len(full.KVs) != len(fast.KVs) {
					t.Fatalf("%s: rev %d key %q: %d full kvs, %d fast", phase, rev, key, len(full.KVs), len(fast.KVs))
				}
				for j := range full.KVs {
					want := &mvccpb.KeyValue{
						Key: full.KVs[j].Key, CreateRevision: full.KVs[j].CreateRevision,
						ModRevision: full.KVs[j].ModRevision, Version: full.KVs[j].Version,
						Lease: full.KVs[j].Lease,
					}
					got := fast.KVs[j]
					if string(got.Key) != string(want.Key) || got.CreateRevision != want.CreateRevision ||
						got.ModRevision != want.ModRevision || got.Version != want.Version || got.Lease != want.Lease {
						t.Errorf("%s: rev %d: fast keys-only %v, full read %v", phase, rev, got, want)
					}
				}
				if end != nil {
					break
				}
			}
		}
	}
}

// TestFastKeysOnlyLeaseRestore: random puts (with random leases, including none) and deletes,
// a compaction, then a restart: before and after the restart (`restoreIntoIndex`), every fast
// keys-only read at every uncompacted revision returns the lease the backend has.
func TestFastKeysOnlyLeaseRestore(t *testing.T) {
	for seed := int64(0); seed < 20; seed++ {
		t.Run(fmt.Sprintf("seed=%d", seed), func(t *testing.T) {
			rnd := mrand.New(mrand.NewSource(seed))
			oldChunk := restoreChunkKeys
			restoreChunkKeys = rnd.Intn(3) + 2
			defer func() { restoreChunkKeys = oldChunk }()

			b, _ := betesting.NewDefaultTmpBackend(t)
			defer b.Close()
			s := NewStore(zaptest.NewLogger(t), b, &lease.FakeLessor{}, StoreConfig{})
			for i := 0; i < 40; i++ {
				k := []byte(fmt.Sprintf("k%d", rnd.Intn(6)))
				switch rnd.Intn(4) {
				case 0:
					s.DeleteRange(k, nil)
				default:
					s.Put(k, []byte("v"), lease.LeaseID(rnd.Intn(3)))
				}
			}
			compactAt := int64(0)
			if rnd.Intn(2) == 0 {
				compactAt = 1 + rnd.Int63n(s.Rev())
				done, err := s.Compact(traceutil.TODO(), compactAt)
				if err != nil {
					t.Fatal(err)
				}
				<-done
			}
			checkFastKeysOnly(t, s, compactAt+1, "live")
			s.Close()

			s = NewStore(zaptest.NewLogger(t), b, &lease.FakeLessor{}, StoreConfig{})
			defer s.Close()
			checkFastKeysOnly(t, s, compactAt+1, "restored")
		})
	}
}
