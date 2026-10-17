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
	"testing"
	"unsafe"

	"go.uber.org/zap/zaptest"

	"go.etcd.io/etcd/server/v3/lease"
	betesting "go.etcd.io/etcd/server/v3/storage/backend/testing"
)

// TestLogicalBytesAlignment reports the offset of store.logicalBytes, which the PR updates
// with atomic.AddInt64/LoadInt64/StoreInt64. On 32-bit platforms (386, arm, mips) the sync/atomic
// 64-bit functions require an 8-byte aligned address, which Go guarantees only for the first word
// of an allocated struct; run with GOARCH=386 to see a misaligned field panic.
func TestLogicalBytesAlignment(t *testing.T) {
	off := unsafe.Offsetof(store{}.logicalBytes)
	t.Logf("GOARCH pointer size %d, offsetof(store.logicalBytes) = %d (mod 8 = %d)",
		unsafe.Sizeof(uintptr(0)), off, off%8)
	b, _ := betesting.NewDefaultTmpBackend(t)
	s := NewStore(zaptest.NewLogger(t), b, &lease.FakeLessor{}, StoreConfig{})
	defer cleanup(s, b)
	s.Put([]byte("foo"), []byte("bar"), lease.NoLease)
	if got := s.LogicalBytes(); got != 6 {
		t.Fatalf("LogicalBytes() = %d, want 6", got)
	}
}
