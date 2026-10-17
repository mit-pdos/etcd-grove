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
	"reflect"
	"testing"

	"go.uber.org/zap/zaptest"

	"go.etcd.io/etcd/server/v3/lease"
	betesting "go.etcd.io/etcd/server/v3/storage/backend/testing"
)

// With the default watchBatchMaxRevs (1000), an unsynced watcher more than 1000 revisions
// behind must still receive every event of its key once syncWatchers has synced it:
//   - "event in window and after": an event of the key inside the first window and another
//     after it (the watcher's batch has 1 revision, so no moreRev);
//   - "event only after": no event of the key in the first window.
//
// syncWatchers is driven by hand (no background loop), so the result is deterministic.
func TestSyncWatchersWindowCutDeliversAll(t *testing.T) {
	for _, tc := range []struct {
		name    string
		inFirst bool
	}{
		{"event in window and after", true},
		{"event only after", false},
	} {
		t.Run(tc.name, func(t *testing.T) {
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

			var want []int64
			if tc.inFirst {
				want = append(want, s.Put([]byte("a"), []byte("v"), lease.NoLease))
			}
			for i := 0; i < 1500; i++ {
				s.Put([]byte("b"), []byte("v"), lease.NoLease)
			}
			want = append(want, s.Put([]byte("a"), []byte("v"), lease.NoLease))

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
				if passes > 100 {
					t.Fatal("did not converge")
				}
			}
			t.Logf("synced after %d passes", passes)
			if !reflect.DeepEqual(got, want) {
				t.Fatalf("got %v, want %v", got, want)
			}
		})
	}
}
