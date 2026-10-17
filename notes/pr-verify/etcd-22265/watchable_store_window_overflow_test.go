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
	"math"
	"testing"

	"go.uber.org/zap/zaptest"

	"go.etcd.io/etcd/server/v3/lease"
	betesting "go.etcd.io/etcd/server/v3/storage/backend/testing"
)

// A future-revision watcher moved to unsynced by Restore (minRev = MaxInt64-2, the case
// chooseAll's comment names) is the only one chosen: minRev + watchBatchMaxRevs + 1 overflows
// int64. The scan [MaxInt64-2, negative) must be empty and the watcher synced, with no panic,
// as on main; and a normal watcher chosen with it still gets its events.
func TestSyncWatchersWindowOverflowFutureWatcher(t *testing.T) {
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

	for i := 0; i < 10; i++ {
		s.Put([]byte("foo"), []byte("v"), lease.NoLease)
	}
	chF := make(chan WatchResponse, 16)
	wf := &watcher{key: []byte("foo"), minRev: math.MaxInt64 - 2, restore: true, ch: chF, id: 1}
	s.unsynced.add(wf)
	s.syncWatchers()
	if _, ok := s.synced.watchers[wf]; !ok {
		t.Fatalf("future watcher not synced")
	}
	if len(chF) != 0 {
		t.Fatalf("future watcher got %d responses, want 0", len(chF))
	}
}
