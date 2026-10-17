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
	"testing"

	"go.uber.org/zap/zaptest"

	"go.etcd.io/etcd/server/v3/lease"
	betesting "go.etcd.io/etcd/server/v3/storage/backend/testing"
)

// A watcher far behind on a key with few events: how many syncWatchers passes until it is
// synced (each pass runs every 100ms in syncWatchersLoop). Logs the count; fails only if the
// watcher misses its event.
func TestSyncWatchersSparseWatcherCatchUpPasses(t *testing.T) {
	b, _ := betesting.NewDefaultTmpBackend(t)
	s := &watchableStore{
		store:    NewStore(zaptest.NewLogger(t), b, &lease.FakeLessor{}, StoreConfig{}),
		victimc:  make(chan struct{}, 1),
		unsynced: newWatcherGroup(),
		synced:   newWatcherGroup(),
		stopc:    make(chan struct{}),
	}
	s.store.ReadView = &readView{s}
	s.store.WriteView = &writeView{s}
	defer cleanup(s, b)

	const others = 20000
	for i := 0; i < others; i++ {
		s.Put([]byte("b"), []byte("v"), lease.NoLease)
	}
	aRev := s.Put([]byte("a"), []byte("v"), lease.NoLease)

	ch := make(chan WatchResponse, 16)
	s.watch([]byte("a"), nil, 1, 0, ch)
	passes := 0
	var got []int64
	for s.unsynced.size() > 0 {
		s.syncWatchers()
		passes++
		for len(ch) > 0 {
			for _, e := range (<-ch).Events {
				got = append(got, e.Kv.ModRevision)
			}
		}
		if passes > 1000 {
			t.Fatal("did not converge")
		}
	}
	t.Logf("watcher on a key with 1 event %d revisions behind: synced after %d syncWatchers passes", others+1, passes)
	if len(got) != 1 || got[0] != aRev {
		t.Fatalf("got %v, want [%d]", got, aRev)
	}
}
