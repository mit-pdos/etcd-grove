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

	"go.etcd.io/etcd/server/v3/lease"
	betesting "go.etcd.io/etcd/server/v3/storage/backend/testing"
)

// Randomized: watchers at random start revisions on a few keys, small channels (victims), a
// small watchBatchMaxRevs (many cohorts and bounded windows), puts interleaved with
// syncWatchers and moveVictims passes driven by hand. Every watcher must receive exactly the
// events of its key from its start revision, in order, once.
func TestSyncWatchersCohortsRandomized(t *testing.T) {
	oldMax := watchBatchMaxRevs
	defer func() { watchBatchMaxRevs = oldMax }()
	for seed := int64(0); seed < 200; seed++ {
		t.Run(fmt.Sprintf("seed=%d", seed), func(t *testing.T) {
			rng := rand.New(rand.NewSource(seed))
			watchBatchMaxRevs = 1 + rng.Intn(6)
			b, _ := betesting.NewDefaultTmpBackend(t)
			s := &watchableStore{
				store:    NewStore(zaptest.NewLogger(t), b, &lease.FakeLessor{}, StoreConfig{}),
				unsynced: newWatcherGroup(),
				synced:   newWatcherGroup(),
				victimc:  make(chan struct{}, 1),
				stopc:    make(chan struct{}),
			}
			// as newWatchableStore does, without starting its loops: writes notify the synced
			// watchers
			s.store.ReadView = &readView{s}
			s.store.WriteView = &writeView{s}
			defer cleanup(s, b)
			keys := []string{"a", "b", "c"}
			type rec struct {
				key   string
				start int64
				ch    chan WatchResponse
				got   []int64
			}
			// revision -> key written
			written := map[int64]string{}
			put := func() {
				k := keys[rng.Intn(len(keys))]
				rev := s.Put([]byte(k), []byte("v"), lease.NoLease)
				written[rev] = k
			}
			for i := 0; i < 20+rng.Intn(60); i++ {
				put()
			}
			var ws []*rec
			for i := 0; i < 2+rng.Intn(8); i++ {
				k := keys[rng.Intn(len(keys))]
				start := 1 + rng.Int63n(s.Rev())
				ch := make(chan WatchResponse, 1+rng.Intn(3))
				s.watch([]byte(k), nil, start, WatchID(i), ch)
				ws = append(ws, &rec{key: k, start: start, ch: ch})
			}
			drain := func(r *rec) {
				for {
					select {
					case wr := <-r.ch:
						for _, e := range wr.Events {
							r.got = append(r.got, e.Kv.ModRevision)
						}
					default:
						return
					}
				}
			}
			for step := 0; step < 400; step++ {
				switch rng.Intn(5) {
				case 0:
					if step < 200 {
						put()
					}
				case 1:
					s.syncWatchers()
				case 2:
					s.moveVictims()
				default:
					drain(ws[rng.Intn(len(ws))])
				}
			}
			for i := 0; i < 2000 && (s.unsynced.size() > 0 || len(s.victims) > 0); i++ {
				for _, r := range ws {
					drain(r)
				}
				s.moveVictims()
				s.syncWatchers()
			}
			for _, r := range ws {
				drain(r)
			}
			if s.unsynced.size() > 0 || len(s.victims) > 0 {
				t.Fatalf("did not converge: unsynced=%d victims=%d", s.unsynced.size(), len(s.victims))
			}
			for i, r := range ws {
				var want []int64
				for rev := r.start; rev <= s.Rev(); rev++ {
					if written[rev] == r.key {
						want = append(want, rev)
					}
				}
				if fmt.Sprint(want) != fmt.Sprint(r.got) {
					t.Fatalf("watcher %d (key %s, start %d, max %d): got %v want %v", i, r.key, r.start, watchBatchMaxRevs, r.got, want)
				}
			}
		})
	}
}
