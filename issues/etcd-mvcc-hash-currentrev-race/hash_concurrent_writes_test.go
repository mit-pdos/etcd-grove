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
	"sync"
	"testing"

	"go.uber.org/zap/zaptest"

	"go.etcd.io/etcd/server/v3/lease"
	betesting "go.etcd.io/etcd/server/v3/storage/backend/testing"
)

// TestHashConcurrentWithWrites runs Hash (what the Maintenance Hash RPC calls,
// on a gRPC goroutine) while the store is written (what the apply loop does).
// The race detector reports a failure if Hash reads the current revision
// without synchronizing with the writes.
func TestHashConcurrentWithWrites(t *testing.T) {
	b, _ := betesting.NewDefaultTmpBackend(t)
	s := NewStore(zaptest.NewLogger(t), b, &lease.FakeLessor{}, StoreConfig{})
	defer cleanup(s, b)

	var wg sync.WaitGroup
	wg.Add(1)
	go func() {
		defer wg.Done()
		for i := 0; i < 200; i++ {
			s.Put([]byte("foo"), []byte("bar"), lease.NoLease)
		}
	}()
	for i := 0; i < 50; i++ {
		if _, _, err := s.HashStorage().Hash(); err != nil {
			t.Fatal(err)
		}
	}
	wg.Wait()
}
