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

	"go.uber.org/zap"
	"go.uber.org/zap/zapcore"
	"go.uber.org/zap/zaptest"

	"go.etcd.io/etcd/pkg/v3/traceutil"
	"go.etcd.io/etcd/server/v3/lease"
	betesting "go.etcd.io/etcd/server/v3/storage/backend/testing"
)

// TestProbeCompactRandomRecreate writes random histories in which write
// transactions delete and put the same keys in one revision (in any order and
// any number of times), compacts at a random revision, and checks that a range
// of the whole keyspace at every revision from the compaction revision to the
// current one answers as before the compaction, both on the compacted store and
// on a store re-opened over the same backend (the index rebuilt from the
// bucket). A failed read (the "range failed to find revision pair" fatal) is
// turned into a panic and reported as a failure.
func TestProbeCompactRandomRecreate(t *testing.T) {
	keys := []string{"a", "b", "c"}
	for seed := int64(0); seed < 300; seed++ {
		t.Run(fmt.Sprint(seed), func(t *testing.T) {
			rnd := rand.New(rand.NewSource(seed))
			lg := zaptest.NewLogger(t, zaptest.Level(zapcore.ErrorLevel),
				zaptest.WrapOptions(zap.WithFatalHook(zapcore.WriteThenPanic)))
			b, _ := betesting.NewDefaultTmpBackend(t)
			s := NewStore(lg, b, &lease.FakeLessor{}, StoreConfig{})
			defer func() { s.Close(); b.Close() }()

			for i := 0; i < 2+rnd.Intn(5); i++ {
				tw := s.Write(traceutil.TODO())
				for j := 0; j < 1+rnd.Intn(4); j++ {
					k := []byte(keys[rnd.Intn(len(keys))])
					switch rnd.Intn(3) {
					case 0:
						tw.DeleteRange(k, nil)
					case 1:
						tw.DeleteRange([]byte("\x00"), []byte("\xff"))
					default:
						tw.Put(k, []byte(fmt.Sprintf("v%d.%d", i, j)), lease.NoLease)
					}
				}
				tw.End()
			}
			cur := s.Rev()
			snapshot := func(s *store, from int64) map[int64]string {
				out := map[int64]string{}
				for r := from; r <= cur; r++ {
					res, err := s.Range(t.Context(), []byte("\x00"), []byte("\xff"), RangeOptions{Rev: r})
					if err != nil {
						t.Fatalf("range at %d: %v", r, err)
					}
					out[r] = fmt.Sprint(res.KVs)
				}
				return out
			}
			c := 1 + rnd.Int63n(cur)
			before := snapshot(s, c)
			ch, err := s.Compact(traceutil.TODO(), c)
			if err != nil {
				t.Fatal(err)
			}
			<-ch
			check := func(name string, s *store) {
				defer func() {
					if p := recover(); p != nil {
						t.Fatalf("%s: compaction at %d (current %d): read panicked: %v", name, c, cur, p)
					}
				}()
				after := snapshot(s, c)
				for r := c; r <= cur; r++ {
					if before[r] != after[r] {
						t.Fatalf("%s: compaction at %d: read at %d: %s, before compaction %s", name, c, r, after[r], before[r])
					}
				}
			}
			check("compacted", s)
			s.Close()
			s = NewStore(lg, b, &lease.FakeLessor{}, StoreConfig{})
			check("re-opened", s)
		})
	}
}
