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

package backend_test

import (
	"path/filepath"
	"testing"
	"time"

	"go.uber.org/zap"

	"go.etcd.io/etcd/server/v3/storage/backend"
	"go.etcd.io/etcd/server/v3/storage/schema"
)

// TestCompactionDeleteVisibleUntilCommit shows the read-side semantics of
// UnsafeDeleteForCompaction: after the batch tx is unlocked, ReadTx and
// ConcurrentReadTx still return the deleted key, and the write tx does not,
// until the next commit (by ForceCommit here; in a server, also the periodic
// commit or any other session's commit). UnsafeDelete is visible at Unlock.
func TestCompactionDeleteVisibleUntilCommit(t *testing.T) {
	for _, compaction := range []bool{false, true} {
		cfg := backend.DefaultBackendConfig(zap.NewNop())
		cfg.Path = filepath.Join(t.TempDir(), "db")
		cfg.BatchInterval = time.Hour
		cfg.BatchLimit = 10000
		be := backend.New(cfg)
		tx := be.BatchTx()
		tx.Lock()
		tx.UnsafeCreateBucket(schema.Test)
		tx.UnsafePut(schema.Test, []byte("k"), []byte("v"))
		tx.Unlock()
		be.ForceCommit()

		tx.Lock()
		if compaction {
			tx.UnsafeDeleteForCompaction(schema.Test, []byte("k"))
		} else {
			tx.UnsafeDelete(schema.Test, []byte("k"))
		}
		wk, _ := tx.UnsafeRange(schema.Test, []byte("k"), nil, 0)
		tx.Unlock()

		rt := be.ReadTx()
		rt.RLock()
		rk, _ := rt.UnsafeRange(schema.Test, []byte("k"), nil, 0)
		rt.RUnlock()
		crt := be.ConcurrentReadTx()
		crt.RLock()
		ck, _ := crt.UnsafeRange(schema.Test, []byte("k"), nil, 0)
		crt.RUnlock()
		t.Logf("compaction=%v: after Unlock, write tx sees %d, ReadTx %d, ConcurrentReadTx %d", compaction, len(wk), len(rk), len(ck))
		if len(wk) != 0 {
			t.Errorf("compaction=%v: write tx still sees the key", compaction)
		}
		want := 0
		if compaction {
			want = 1
		}
		if len(rk) != want || len(ck) != want {
			t.Errorf("compaction=%v: readers see %d/%d keys after Unlock, want %d", compaction, len(rk), len(ck), want)
		}

		be.ForceCommit()
		rt.RLock()
		rk, _ = rt.UnsafeRange(schema.Test, []byte("k"), nil, 0)
		rt.RUnlock()
		if len(rk) != 0 {
			t.Errorf("compaction=%v: ReadTx sees the key after ForceCommit", compaction)
		}
		be.Close()
	}
}
