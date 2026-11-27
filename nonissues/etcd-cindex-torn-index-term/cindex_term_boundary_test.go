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

package etcdserver

import (
	"path/filepath"
	"sync"
	"sync/atomic"
	"testing"
	"time"

	"go.uber.org/zap"

	"go.etcd.io/etcd/pkg/v3/notify"
	"go.etcd.io/etcd/pkg/v3/wait"
	"go.etcd.io/etcd/server/v3/etcdserver/cindex"
	serverstorage "go.etcd.io/etcd/server/v3/storage"
	"go.etcd.io/etcd/server/v3/storage/backend"
	"go.etcd.io/etcd/server/v3/storage/schema"
	"go.etcd.io/raft/v3/raftpb"
)

// checkPairHooks runs etcd's pre-commit hook and reads back, in the same transaction, the pair it
// saved.
type checkPairHooks struct {
	*serverstorage.BackendHooks
	torn  *atomic.Uint64
	saves *atomic.Uint64
}

func (h checkPairHooks) OnPreCommitUnsafe(tx backend.UnsafeReadWriter) {
	h.BackendHooks.OnPreCommitUnsafe(tx)
	h.saves.Add(1)
	if idx, term := schema.UnsafeReadConsistentIndex(tx); idx != term {
		h.torn.CompareAndSwap(0, idx<<32|term)
	}
}

// TestEmptyEntrySavesConsistentIndexWithItsTerm: the apply loop applies the empty entry a new
// leader appends at the start of its term (applyEntryNormal moves the consistent index to it
// outside the backend's batch lock), while the backend's commit loop saves the consistent index and
// its term (BackendHooks.OnPreCommitUnsafe). Every entry here starts a new term (term = index), so
// every saved pair must have term = index; a commit between the two halves of the set saves the
// new index with the previous term. Another writer keeps the batch pending (as other entries'
// writes, the lessor's checkpoints or the compactor do), so the commit loop commits.
func TestEmptyEntrySavesConsistentIndexWithItsTerm(t *testing.T) {
	lg := zap.NewNop()
	ci := cindex.NewConsistentIndex(nil)
	bcfg := backend.DefaultBackendConfig(lg)
	bcfg.Path = filepath.Join(t.TempDir(), "db")
	bcfg.BatchInterval = 10 * time.Microsecond
	bcfg.UnsafeNoFsync = true
	var torn, saves atomic.Uint64
	bcfg.Hooks = checkPairHooks{serverstorage.NewBackendHooks(lg, ci), &torn, &saves}
	be := backend.New(bcfg)
	defer be.Close()
	ci.SetBackend(be)
	schema.CreateMetaBucket(be.BatchTx())
	ci.SetConsistentIndex(1, 1)

	s := &EtcdServer{
		lgMu: new(sync.RWMutex), lg: lg, be: be, consistIndex: ci, memberID: 1,
		firstCommitInTerm: notify.NewNotifier(), w: wait.New(), applyWait: wait.NewTimeList(),
	}
	var ep etcdProgress

	// Another writer (the lessor's checkpoints, the compactor, the apply of other entries) keeps the
	// batch pending, so the commit loop commits.
	var stop atomic.Bool
	var wg sync.WaitGroup
	wg.Add(1)
	go func() {
		defer wg.Done()
		for !stop.Load() {
			tx := be.BatchTx()
			tx.LockOutsideApply()
			tx.UnsafePut(schema.Meta, []byte("zz-other-writer"), []byte("x"))
			tx.Unlock()
			time.Sleep(10 * time.Microsecond)
		}
	}()
	defer func() { stop.Store(true); wg.Wait() }()
	deadline := time.Now().Add(5 * time.Second)
	i := uint64(2)
	defer func() { t.Logf("%d entries applied, %d backend commits", i-2, saves.Load()) }()
	for ; time.Now().Before(deadline) && torn.Load() == 0; i++ {
		e := &raftpb.Entry{Type: raftpb.EntryType_EntryNormal.Enum(), Index: new(i), Term: new(i)}
		s.apply([]*raftpb.Entry{e}, &ep, nil)
	}
	if v := torn.Load(); v != 0 {
		t.Fatalf("the backend saved consistent index %d with term %d", v>>32, v&0xffffffff)
	}
}
