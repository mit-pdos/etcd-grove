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
	"context"
	"math"
	"reflect"
	"testing"
	"time"

	"go.uber.org/zap/zaptest"

	"go.etcd.io/etcd/pkg/v3/traceutil"
	"go.etcd.io/etcd/server/v3/lease"
	betesting "go.etcd.io/etcd/server/v3/storage/backend/testing"
)

// collect reads events from a watch stream until it has n of them or nothing arrives for
// quiet; it returns the events' revisions.
func reviewCollect(t *testing.T, ws WatchStream, n int, quiet time.Duration) []int64 {
	var got []int64
	for len(got) < n {
		select {
		case resp := <-ws.Chan():
			for _, e := range resp.Events {
				got = append(got, e.Kv.ModRevision)
			}
		case <-time.After(quiet):
			return got
		}
	}
	return got
}

// The real store (New: syncWatchersLoop and syncVictimsLoop running), the real watch API,
// default constants (watchBatchMaxRevs = 1000): a watcher on "a" from revision 1, with an
// event of "a" at revision 2, 1500 revisions of other keys, then "a" again.
func TestReviewRealStoreWindowCut(t *testing.T) {
	b, _ := betesting.NewDefaultTmpBackend(t)
	s := New(zaptest.NewLogger(t), b, &lease.FakeLessor{}, StoreConfig{})
	defer cleanup(s, b)

	want := []int64{s.Put([]byte("a"), []byte("v"), lease.NoLease)}
	for i := 0; i < 1500; i++ {
		s.Put([]byte("b"), []byte("v"), lease.NoLease)
	}
	want = append(want, s.Put([]byte("a"), []byte("v"), lease.NoLease))

	ws := s.NewWatchStream()
	defer ws.Close()
	if _, err := ws.Watch(context.TODO(), 0, []byte("a"), nil, 1); err != nil {
		t.Fatal(err)
	}
	if got := reviewCollect(t, ws, len(want), 3*time.Second); !reflect.DeepEqual(got, want) {
		t.Fatalf("got %v, want %v", got, want)
	}
}

// The PR's own scenario: a single watcher whose key has an event at every revision from its
// start revision on, 3000 revisions behind. Every window of 1001 revisions then holds 1001
// event revisions, so the batch overflows, moreRev is set and the next pass resumes there:
// this case is correct with the PR.
func TestReviewRealStoreEveryRevisionSingleWatcher(t *testing.T) {
	b, _ := betesting.NewDefaultTmpBackend(t)
	s := New(zaptest.NewLogger(t), b, &lease.FakeLessor{}, StoreConfig{})
	defer cleanup(s, b)

	var want []int64
	for i := 0; i < 3000; i++ {
		want = append(want, s.Put([]byte("a"), []byte("v"), lease.NoLease))
	}
	ws := s.NewWatchStream()
	defer ws.Close()
	if _, err := ws.Watch(context.TODO(), 0, []byte("a"), nil, want[0]); err != nil {
		t.Fatal(err)
	}
	if got := reviewCollect(t, ws, len(want), 3*time.Second); !reflect.DeepEqual(got, want) {
		t.Fatalf("got %d events (last %v), want %d", len(got), got[len(got)-1:], len(want))
	}
}

func reviewHandStore(t *testing.T) (*watchableStore, func()) {
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
	return s, func() { cleanup(s, b) }
}

// Even when the key has an event at every revision, two watchers chosen together at
// different start revisions: the window starts at the older one's, so the younger one's batch
// has fewer than watchBatchMaxRevs revisions, no moreRev, and it is synced at curRev+1,
// skipping the rest. syncWatchers is driven by hand (both watchers in one pass).
func TestReviewEveryRevisionTwoWatchers(t *testing.T) {
	s, done := reviewHandStore(t)
	defer done()

	var revs []int64
	for i := 0; i < 3000; i++ {
		revs = append(revs, s.Put([]byte("a"), []byte("v"), lease.NoLease))
	}
	chA := make(chan WatchResponse, 64)
	chB := make(chan WatchResponse, 64)
	s.watch([]byte("a"), nil, revs[0], 1, chA)
	s.watch([]byte("a"), nil, revs[500], 2, chB)
	got := map[chan WatchResponse][]int64{}
	for pass := 0; s.unsynced.size() > 0; pass++ {
		if pass > 100 {
			t.Fatal("did not converge")
		}
		s.syncWatchers()
		for _, ch := range []chan WatchResponse{chA, chB} {
			for len(ch) > 0 {
				for _, e := range (<-ch).Events {
					got[ch] = append(got[ch], e.Kv.ModRevision)
				}
			}
		}
	}
	if len(got[chA]) != 3000 {
		t.Errorf("watcher from %d: got %d events, want 3000", revs[0], len(got[chA]))
	}
	if len(got[chB]) != 2500 {
		t.Errorf("watcher from %d: got %d events (last %d), want 2500 (last %d)",
			revs[500], len(got[chB]), got[chB][len(got[chB])-1], revs[2999])
	}
}

// All chosen watchers compacted and unable to take the compaction response (full channel):
// chooseAll returns MaxInt64 and minRev + watchBatchMaxRevs + 1 wraps to a negative int64.
// The scan [MaxInt64, negative) is still empty (as bytes, [0x7fff..., 0x8000...03e8) holds no
// revision key), nothing panics, and the watcher stays unsynced for a retry, as on main.
func TestReviewAllCompactedOverflow(t *testing.T) {
	s, done := reviewHandStore(t)
	defer done()

	for i := 0; i < 10; i++ {
		s.Put([]byte("a"), []byte("v"), lease.NoLease)
	}
	if _, err := s.Compact(traceutil.TODO(), 5); err != nil {
		t.Fatal(err)
	}
	ch := make(chan WatchResponse) // unbuffered, no reader: the compaction response cannot be sent
	w := &watcher{key: []byte("a"), minRev: 2, ch: ch, id: 1}
	s.unsynced.add(w)
	if _, minRev := s.unsynced.choose(maxWatchersPerSync, s.store.currentRev, s.store.compactMainRev); minRev != math.MaxInt64 {
		t.Fatalf("minRev = %d, want MaxInt64", minRev)
	}
	if n := s.syncWatchers(); n != 1 {
		t.Fatalf("unsynced = %d, want 1", n)
	}
	if w.minRev != 2 {
		t.Fatalf("w.minRev = %d, want 2", w.minRev)
	}
}
