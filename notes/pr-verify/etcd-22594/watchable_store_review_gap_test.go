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

// TestReviewSyncWatchersCutScanSkipsGapEvenWithMoreRev: when the bounded scan is cut and part
// of the range is in the read buffer, UnsafeRange returns bbolt's first entries and then the
// buffer's, skipping the entries in between. A watcher whose batch then overflows (moreRev set,
// so it stays unsynced, the case the PR relies on) still skips the event in the gap: it is
// given the buffer's events and its minRev is moved past the gap.
//
// Deterministic: no sync loops (newWatchableStore), no periodic commit (1h interval).
func TestReviewSyncWatchersCutScanSkipsGapEvenWithMoreRev(t *testing.T) {
	b, _ := betesting.NewTmpBackend(t, time.Hour, 1<<30)
	s := newWatchableStore(zaptest.NewLogger(t), b, &lease.FakeLessor{}, StoreConfig{})
	oldMaxRevs := watchBatchMaxRevs
	defer func() {
		watchBatchMaxRevs = oldMaxRevs
		s.store.Close()
		b.Close()
	}()
	watchBatchMaxRevs = 1 // scan limit 1 * 512 * 2 = 1024 entries

	put := func(k string) {
		txn := s.Write(traceutil.TODO())
		txn.Put([]byte(k), []byte("v"), lease.NoLease)
		txn.End()
	}
	var want []int64
	// revisions 2..1101 committed to bbolt; "a" at revision 1052 (in the gap of a cut scan).
	for i := 0; i < 1100; i++ {
		if i == 1050 {
			put("a")
			want = append(want, int64(i+2))
		} else {
			put("b")
		}
	}
	b.ForceCommit()
	// revisions 1102, 1103 in the read buffer (not committed).
	put("a")
	put("a")
	want = append(want, 1102, 1103)

	ch := make(chan WatchResponse, 100)
	s.watch([]byte("a"), nil, 1, 0, ch)

	var got []int64
	for i := 0; i < 10 && s.unsynced.size() > 0; i++ {
		s.syncWatchers()
	}
	close(ch)
	for resp := range ch {
		for _, e := range resp.Events {
			got = append(got, e.Kv.ModRevision)
		}
	}
	if len(got) != len(want) {
		t.Fatalf("watcher on %q from revision 1 got events at revisions %v, want %v", "a", got, want)
	}
	for i := range want {
		if got[i] != want[i] {
			t.Fatalf("watcher on %q from revision 1 got events at revisions %v, want %v", "a", got, want)
		}
	}
}
