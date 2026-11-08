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

// TestProgressCommitEndDeadlock runs a progress request while a write
// transaction is open and a Commit waits for it: the write's End must return.
func TestProgressCommitEndDeadlock(t *testing.T) {
	b, _ := betesting.NewDefaultTmpBackend(t)
	s := New(zap.NewNop(), b, &lease.FakeLessor{}, StoreConfig{})

	ws := s.NewWatchStream()
	id, err := ws.Watch(context.TODO(), 0, []byte("a"), nil, 0) // synced
	if err != nil {
		t.Fatal(err)
	}
	tw := s.Write(traceutil.TODO())
	tw.Put([]byte("a"), []byte("1"), lease.NoLease)
	go s.Commit() // waits for store.mu behind tw
	time.Sleep(100 * time.Millisecond)
	go ws.RequestProgress(id) // holds watchableStore.mu, waits for store.mu behind Commit
	time.Sleep(100 * time.Millisecond)
	done := make(chan struct{})
	go func() { tw.End(); close(done) }() // waits for watchableStore.mu
	select {
	case <-done:
	case <-time.After(3 * time.Second):
		t.Fatal("the write transaction's End did not return: RequestProgress, Commit and End wait on each other")
	}
	ws.Close()
	s.Close()
	b.Close()
}
