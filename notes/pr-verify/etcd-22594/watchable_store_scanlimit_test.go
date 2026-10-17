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
	"time"

	"go.uber.org/zap/zaptest"

	"go.etcd.io/etcd/pkg/v3/traceutil"
	"go.etcd.io/etcd/server/v3/lease"
	betesting "go.etcd.io/etcd/server/v3/storage/backend/testing"
)

// TestSyncWatchersScanLimitDeliversAll: an unsynced watcher must receive every event on its
// key, however many revisions of other keys lie between its start revision and its events.
// With the scan of syncWatchers bounded by an entry count (watchBatchMaxRevs *
// maxWatchersPerSync * 2), a watcher whose events lie past the bounded scan is moved to the
// synced group at the current revision and never receives them.
func TestSyncWatchersScanLimitDeliversAll(t *testing.T) {
	tcs := []struct {
		name string
		// puts of "a" at these positions among `total` puts (the others are of "b")
		aAt   []int
		total int
	}{
		{name: "event of the watched key only past the scan", aAt: []int{1100}, total: 1101},
		{name: "one event inside the scan, one past it", aAt: []int{10, 1100}, total: 1101},
	}
	for _, tc := range tcs {
		t.Run(tc.name, func(t *testing.T) {
			b, _ := betesting.NewDefaultTmpBackend(t)
			s := New(zaptest.NewLogger(t), b, &lease.FakeLessor{}, StoreConfig{})
			oldMaxRevs := watchBatchMaxRevs
			defer func() {
				watchBatchMaxRevs = oldMaxRevs
				cleanup(s, b)
			}()
			// The PR's scan limit is then 1 * 512 * 2 = 1024 entries; at the default (1000)
			// it is 1,024,000 entries and the same happens with 1,024,000 puts of "b".
			watchBatchMaxRevs = 1

			isA := map[int]bool{}
			for _, i := range tc.aAt {
				isA[i] = true
			}
			var want []int64
			for i := 0; i < tc.total; i++ {
				k := []byte("b")
				if isA[i] {
					k = []byte("a")
				}
				txn := s.Write(traceutil.TODO())
				txn.Put(k, []byte("v"), lease.NoLease)
				txn.End()
				if isA[i] {
					want = append(want, int64(i+2)) // revisions start at 2
				}
			}

			// Commit the puts to bbolt, so that the scan reads them all from bbolt (not
			// partly from the read buffer, which a periodic commit would make timing
			// dependent).
			b.ForceCommit()

			w := s.NewWatchStream()
			defer w.Close()
			w.Watch(t.Context(), 0, []byte("a"), nil, 1)

			var got []int64
			timeout := time.After(3 * time.Second)
			for len(got) < len(want) {
				select {
				case resp := <-w.Chan():
					for _, e := range resp.Events {
						got = append(got, e.Kv.ModRevision)
					}
				case <-timeout:
					t.Fatalf("watcher on %q from revision 1 got events at revisions %v, want %v", "a", got, want)
				}
			}
			if len(got) != len(want) {
				t.Fatalf("got %v, want %v", got, want)
			}
			for i := range want {
				if got[i] != want[i] {
					t.Fatalf("got %v, want %v", got, want)
				}
			}
		})
	}
}
