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
	"sync"
	"sync/atomic"
	"testing"

	"go.uber.org/zap"

	"go.etcd.io/etcd/pkg/v3/traceutil"
	"go.etcd.io/etcd/server/v3/lease"
	betesting "go.etcd.io/etcd/server/v3/storage/backend/testing"
)

// TestHashByRevDuringRestore calls HashByRev for a compacted revision (what the
// HashKV RPC and the compaction hash check do, on other goroutines) while the
// store is restored from a backend (what applying a snapshot from the leader
// does). The current revision returned with a hash of revision r must be at
// least r: the store had revision r.
func TestHashByRevDuringRestore(t *testing.T) {
	b, _ := betesting.NewDefaultTmpBackend(t)
	s := NewStore(zap.NewNop(), b, &lease.FakeLessor{}, StoreConfig{})
	defer cleanup(s, b)

	for i := 0; i < 1000; i++ {
		s.Put([]byte(fmt.Sprintf("foo%04d", i)), []byte("bar"), lease.NoLease)
	}
	const compactRev = 500
	ch, err := s.Compact(traceutil.TODO(), compactRev)
	if err != nil {
		t.Fatal(err)
	}
	<-ch

	var stop atomic.Bool
	var low atomic.Int64
	low.Store(1 << 62)
	var wg sync.WaitGroup
	wg.Add(1)
	go func() {
		defer wg.Done()
		for !stop.Load() {
			h, cur, err := s.HashStorage().HashByRev(compactRev)
			if err == nil && h.Revision == compactRev && cur < low.Load() {
				low.Store(cur)
			}
		}
	}()
	for i := 0; i < 100; i++ {
		if err := s.Restore(b); err != nil {
			t.Fatal(err)
		}
	}
	stop.Store(true)
	wg.Wait()
	if l := low.Load(); l < compactRev {
		t.Errorf("HashByRev(%d) returned current revision %d, below the revision hashed (the store is at %d)", compactRev, l, s.Rev())
	}
}
