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

// The regression test of etcd-io/etcd#22185 (at aad3f3a2b), as a file of its own.

package mvcc

import (
	"testing"
	"time"

	"go.uber.org/zap/zaptest"

	"go.etcd.io/etcd/pkg/v3/traceutil"
	"go.etcd.io/etcd/server/v3/lease"
	betesting "go.etcd.io/etcd/server/v3/storage/backend/testing"
)

// TestProgressIfSyncDeadlock reproduces the three-way lock cycle in which
// progressIfSync (holding watchable.mu, waiting on store.mu via s.rev()), an
// in-flight write txn (holding store.mu, waiting on watchable.mu in End()), and
// a concurrent Commit (waiting on store.mu) deadlock the apply loop. It fails if
// End() cannot complete, i.e. if progressIfSync takes store.mu while holding
// watchable.mu.
func TestProgressIfSyncDeadlock(t *testing.T) {
	b, _ := betesting.NewDefaultTmpBackend(t)
	// Use newWatchableStore (no background sync/victim loops) for a controlled interleaving.
	s := newWatchableStore(zaptest.NewLogger(t), b, &lease.FakeLessor{}, StoreConfig{})
	defer func() { _ = s.store.Close() }()

	// W: open a write txn -> now holding store.mu.RLock until End().
	tw := s.Write(traceutil.TODO())
	tw.Put([]byte("k"), []byte("v"), lease.NoLease)

	// C: Commit wants store.mu.Lock; it blocks behind W's RLock and queues the writer,
	// which makes subsequent store.mu.RLock callers block (RWMutex writer preference).
	go func() { s.Commit() }()
	time.Sleep(100 * time.Millisecond)

	// P: progressIfSync grabs watchable.mu.RLock, then blocks on store.mu.RLock behind C.
	go func() { s.progressAll(map[WatchID]*watcher{}) }()
	time.Sleep(100 * time.Millisecond)

	// W: End() now wants watchable.mu.Lock, held (RLock) by P -> cycle closes unless
	// progressIfSync avoids taking store.mu while holding watchable.mu.
	done := make(chan struct{})
	go func() {
		tw.End()
		close(done)
	}()

	select {
	case <-done:
	case <-time.After(3 * time.Second):
		t.Fatal("deadlock: write txn End() blocked on watchable.mu while progressIfSync holds it and waits on store.mu")
	}
}
