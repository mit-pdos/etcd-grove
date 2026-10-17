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

	"go.uber.org/zap/zaptest"

	"go.etcd.io/etcd/pkg/v3/traceutil"
	"go.etcd.io/etcd/server/v3/lease"
	betesting "go.etcd.io/etcd/server/v3/storage/backend/testing"
)

// livePayloadOf is what etcd_mvcc_live_kv_payload_bytes is documented to be: the sum of
// len(key)+len(value) over the latest non-deleted version of each key.
func livePayloadOf(t *testing.T, kv KV) int {
	t.Helper()
	r, err := kv.Range(t.Context(), []byte{0}, []byte{0xff}, RangeOptions{})
	if err != nil {
		t.Fatal(err)
	}
	n := 0
	for _, item := range r.KVs {
		n += len(item.Key) + len(item.Value)
	}
	return n
}

// TestLiveKVPayloadRandomized drives random histories (puts, overwrites, empty values,
// single and range deletes, multi-operation transactions, compactions at random revisions,
// restarts and Restore onto the same backend) with a small restore chunk, so that restoring
// evicts key indexes from restoreIntoIndex's cache, and checks after every step that the gauge
// equals the payload of the current state.
func TestLiveKVPayloadRandomized(t *testing.T) {
	oldChunk := restoreChunkKeys
	restoreChunkKeys = 7
	defer func() { restoreChunkKeys = oldChunk }()

	for seed := int64(0); seed < 40; seed++ {
		t.Run(fmt.Sprintf("seed=%d", seed), func(t *testing.T) {
			rng := rand.New(rand.NewSource(seed))
			b, _ := betesting.NewDefaultTmpBackend(t)
			s := NewStore(zaptest.NewLogger(t), b, &lease.FakeLessor{}, StoreConfig{})
			key := func() []byte { return []byte(fmt.Sprintf("k%02d", rng.Intn(30))) }
			val := func() []byte {
				v := make([]byte, rng.Intn(12))
				for i := range v {
					v[i] = byte('a' + rng.Intn(26))
				}
				return v
			}
			check := func(step int, what string) {
				t.Helper()
				if got, want := readGaugeInt(liveKVPayloadGauge), livePayloadOf(t, s); got != want {
					t.Fatalf("step %d (%s): live KV payload gauge = %d, want %d", step, what, got, want)
				}
			}
			check(-1, "start")
			for step := 0; step < 300; step++ {
				switch op := rng.Intn(100); {
				case op < 45:
					s.Put(key(), val(), lease.NoLease)
					check(step, "put")
				case op < 60:
					s.DeleteRange(key(), nil)
					check(step, "delete")
				case op < 65:
					k1, k2 := key(), key()
					if string(k1) > string(k2) {
						k1, k2 = k2, k1
					}
					s.DeleteRange(k1, k2)
					check(step, "range delete")
				case op < 80:
					txn := s.Write(traceutil.TODO())
					for i := rng.Intn(5); i >= 0; i-- {
						if rng.Intn(3) == 0 {
							txn.DeleteRange(key(), nil)
						} else {
							txn.Put(key(), val(), lease.NoLease)
						}
					}
					txn.End()
					check(step, "txn")
				case op < 88:
					rev := s.Rev()
					if rev > 1 {
						at := 1 + rng.Int63n(rev)
						if ch, err := s.Compact(traceutil.TODO(), at); err == nil {
							<-ch
						}
					}
					check(step, "compact")
				case op < 94:
					s.Close()
					s = NewStore(zaptest.NewLogger(t), b, &lease.FakeLessor{}, StoreConfig{})
					check(step, "restart")
				default:
					s.Commit()
					if err := s.Restore(b); err != nil {
						t.Fatal(err)
					}
					check(step, "restore")
				}
			}
			cleanup(s, b)
		})
	}
}
