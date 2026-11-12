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
	"testing"
	"time"

	"go.uber.org/zap"

	"go.etcd.io/etcd/pkg/v3/traceutil"
	"go.etcd.io/etcd/server/v3/lease"
	betesting "go.etcd.io/etcd/server/v3/storage/backend/testing"
)

// TestWatchFromCompactRevSameKeyTwice watches, from a revision that puts one
// key twice, before and after a compaction at that revision: the watch should
// get the same events both times, or a compaction response.
func TestWatchFromCompactRevSameKeyTwice(t *testing.T) {
	b, _ := betesting.NewDefaultTmpBackend(t)
	s := New(zap.NewNop(), b, &lease.FakeLessor{}, StoreConfig{})
	defer cleanup(s, b)

	tw := s.Write(traceutil.TODO())
	tw.Put([]byte("a"), []byte("v1"), lease.NoLease)
	tw.Put([]byte("a"), []byte("v2"), lease.NoLease)
	tw.End()
	c := s.Rev()                                   // 2
	s.Put([]byte("b"), []byte("x"), lease.NoLease) // 3

	count := func() int {
		ws := s.NewWatchStream()
		defer ws.Close()
		if _, err := ws.Watch(context.TODO(), 0, []byte("a"), nil, c); err != nil {
			t.Fatal(err)
		}
		n := 0
		timeout := time.After(500 * time.Millisecond)
		for {
			select {
			case r := <-ws.Chan():
				if r.CompactRevision != 0 {
					t.Fatalf("compacted response %d", r.CompactRevision)
				}
				n += len(r.Events)
			case <-timeout:
				return n
			}
		}
	}
	before := count()
	ch, err := s.Compact(traceutil.TODO(), c)
	if err != nil {
		t.Fatal(err)
	}
	<-ch
	after := count()
	if before != after {
		t.Errorf("watch from the compaction revision %d: %d events before the compaction, %d after", c, before, after)
	}
}
