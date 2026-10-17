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
	"errors"
	"testing"
	"time"

	"go.uber.org/zap/zaptest"

	"go.etcd.io/etcd/pkg/v3/traceutil"
	"go.etcd.io/etcd/server/v3/lease"
	"go.etcd.io/etcd/server/v3/storage/backend"
	betesting "go.etcd.io/etcd/server/v3/storage/backend/testing"
)

// TestStoreCompactLatestRevisionTwice: compacting the head twice is a no-op
// (nil, a channel that closes), compacting a revision the head moved past is
// ErrCompacted, and the no-op also holds after the store is reopened.
func TestStoreCompactLatestRevisionTwice(t *testing.T) {
	b, tmpPath := betesting.NewDefaultTmpBackend(t)
	s := NewStore(zaptest.NewLogger(t), b, &lease.FakeLessor{}, StoreConfig{})

	for i := 0; i < 5; i++ {
		s.Put([]byte("foo"), []byte("bar"), lease.NoLease)
	}
	head := s.Rev()
	wait := func(ch <-chan struct{}) {
		t.Helper()
		select {
		case <-ch:
		case <-time.After(10 * time.Second):
			t.Fatal("compaction channel did not close")
		}
	}

	ch, err := s.Compact(traceutil.TODO(), head)
	if err != nil {
		t.Fatalf("first Compact(%d) = %v", head, err)
	}
	wait(ch)

	ch, err = s.Compact(traceutil.TODO(), head)
	if err != nil {
		t.Fatalf("second Compact(%d) at the head = %v, want nil", head, err)
	}
	if ch == nil {
		t.Fatalf("second Compact(%d) returned a nil channel", head)
	}
	wait(ch)

	if _, err = s.Compact(traceutil.TODO(), head-1); !errors.Is(err, ErrCompacted) {
		t.Fatalf("Compact(%d) below the compaction revision = %v, want ErrCompacted", head-1, err)
	}

	// Reopen: the compaction revision and the head are both `head`.
	s.Close()
	b.Close()
	b = backend.NewDefaultBackend(zaptest.NewLogger(t), tmpPath)
	s = NewStore(zaptest.NewLogger(t), b, &lease.FakeLessor{}, StoreConfig{})
	if s.Rev() != head {
		t.Fatalf("reopened Rev() = %d, want %d", s.Rev(), head)
	}
	ch, err = s.Compact(traceutil.TODO(), head)
	if err != nil {
		t.Fatalf("Compact(%d) at the head after reopen = %v, want nil", head, err)
	}
	wait(ch)

	// A write moves the head: the old head is now ErrCompacted.
	s.Put([]byte("foo"), []byte("baz"), lease.NoLease)
	if _, err = s.Compact(traceutil.TODO(), head); !errors.Is(err, ErrCompacted) {
		t.Fatalf("Compact(%d) after a write = %v, want ErrCompacted", head, err)
	}
	s.Close()
	b.Close()
}
