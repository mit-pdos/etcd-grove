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

package cindex

import (
	"sync"
	"sync/atomic"
	"testing"
	"time"

	betesting "go.etcd.io/etcd/server/v3/storage/backend/testing"
	"go.etcd.io/etcd/server/v3/storage/schema"
)

// TestConsistentIndexSavesTermOfIndex: the apply loop sets the consistent index and its term
// outside the backend's batch lock (applyEntryNormal's deferred set, a refused conf change) while
// the backend's commit saves them (UnsafeSave). The saved term must be the term of the saved
// index: a restart whose WAL lacks that entry starts raft at a snapshot labelled with it.
// The writer sets (i, i); every saved pair must have equal index and term.
func TestConsistentIndexSavesTermOfIndex(t *testing.T) {
	be, _ := betesting.NewDefaultTmpBackend(t)
	defer betesting.Close(t, be)
	tx := be.BatchTx()
	tx.Lock()
	schema.UnsafeCreateMetaBucket(tx)
	tx.Unlock()

	ci := NewConsistentIndex(be)
	ci.SetConsistentIndex(1, 1)

	var stop atomic.Bool
	var wg sync.WaitGroup
	wg.Add(1)
	go func() {
		defer wg.Done()
		for i := uint64(2); !stop.Load(); i++ {
			ci.SetConsistentIndex(i, i)
		}
	}()
	torn, saves := 0, 0
	deadline := time.Now().Add(time.Second)
	for time.Now().Before(deadline) && torn == 0 {
		tx.Lock()
		ci.UnsafeSave(tx)
		idx, term := schema.UnsafeReadConsistentIndex(tx)
		tx.Unlock()
		saves++
		if idx != term {
			torn++
			t.Logf("saved consistent index %d with term %d", idx, term)
		}
	}
	stop.Store(true)
	wg.Wait()
	t.Logf("%d saves", saves)
	if torn != 0 {
		t.Fatalf("a save paired a consistent index with another index's term")
	}
}
