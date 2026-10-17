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

// TestRangeEventsLimitIsPrefix: with a limit that cuts the range, rangeEvents should return
// the first `limit` events of [minRev, maxRev). The read transaction's UnsafeRange with a limit
// returns bbolt's first entries and then all of the read buffer's (the latest, not yet
// committed writes), so the result skips the revisions between them.
func TestRangeEventsLimitIsPrefix(t *testing.T) {
	// A long batch interval: the puts after ForceCommit stay in the read buffer.
	b, _ := betesting.NewTmpBackend(t, time.Hour, 10000)
	s := New(zaptest.NewLogger(t), b, &lease.FakeLessor{}, StoreConfig{})
	defer cleanup(s, b)

	put := func(n int) {
		for i := 0; i < n; i++ {
			txn := s.Write(traceutil.TODO())
			txn.Put([]byte("k"), []byte("v"), lease.NoLease)
			txn.End()
		}
	}
	put(20) // revisions 2..21, committed to bbolt below
	b.ForceCommit()
	put(5) // revisions 22..26, in the read buffer

	evs := rangeEvents(zaptest.NewLogger(t), b, 2, 27, 10, fakeContains{})
	var got []int64
	for _, ev := range evs {
		got = append(got, ev.Kv.ModRevision)
	}
	want := []int64{2, 3, 4, 5, 6, 7, 8, 9, 10, 11}
	if len(got) != len(want) {
		t.Fatalf("rangeEvents(2, 27, limit 10) = revisions %v, want %v", got, want)
	}
	for i := range want {
		if got[i] != want[i] {
			t.Fatalf("rangeEvents(2, 27, limit 10) = revisions %v, want %v", got, want)
		}
	}
}
