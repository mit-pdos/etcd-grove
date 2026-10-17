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

package wal

import (
	"os"
	"path/filepath"
	"testing"

	"go.uber.org/zap/zaptest"
	"google.golang.org/protobuf/proto"

	"go.etcd.io/etcd/server/v3/storage/wal/walpb"
	"go.etcd.io/raft/v3/raftpb"
)

// TestSaveCommitOnlyHardStateIsNotDurable shows that WAL.Save returns before
// a HardState that only advances Commit reaches the disk: raft.MustSync is
// false for it, so Save neither syncs nor flushes the encoder's buffer. A
// copy of the WAL directory taken right after Save returns (what a crash
// leaves) still holds the old commit index.
//
// etcd-io/etcd#22223's asynchronous path closes an apply barrier as soon as
// the append worker's Save returns, and documents the barrier as keeping
// "the durable backend consistent index from advancing beyond the durable
// WAL HardState commit". For a Ready whose MsgStorageAppend carries only the
// new commit (the entries were made durable by an earlier append, which is
// what raft's asynchronous mode requires before it hands them to the apply
// thread) the barrier is closed while the new commit is still in memory.
func TestSaveCommitOnlyHardStateIsNotDurable(t *testing.T) {
	lg := zaptest.NewLogger(t)
	dir := filepath.Join(t.TempDir(), "wal")
	w, err := Create(lg, dir, nil)
	if err != nil {
		t.Fatal(err)
	}
	defer w.Close()

	// An append with entries: synced.
	ents := []*raftpb.Entry{{Index: proto.Uint64(1), Term: proto.Uint64(1), Data: []byte("x")}}
	hs1 := &raftpb.HardState{Term: proto.Uint64(1), Vote: proto.Uint64(1), Commit: proto.Uint64(0)}
	if err := w.Save(hs1, ents); err != nil {
		t.Fatal(err)
	}
	// The commit advances, nothing else: Save returns without syncing.
	hs2 := &raftpb.HardState{Term: proto.Uint64(1), Vote: proto.Uint64(1), Commit: proto.Uint64(1)}
	if err := w.Save(hs2, nil); err != nil {
		t.Fatal(err)
	}

	// What a crash right now leaves on disk: a copy of the directory.
	crash := filepath.Join(t.TempDir(), "crash")
	if err := os.MkdirAll(crash, 0o700); err != nil {
		t.Fatal(err)
	}
	names, err := readWALNames(lg, dir)
	if err != nil {
		t.Fatal(err)
	}
	for _, n := range names {
		b, err := os.ReadFile(filepath.Join(dir, n))
		if err != nil {
			t.Fatal(err)
		}
		if err := os.WriteFile(filepath.Join(crash, n), b, 0o600); err != nil {
			t.Fatal(err)
		}
	}
	r, err := Open(lg, crash, &walpb.Snapshot{})
	if err != nil {
		t.Fatal(err)
	}
	defer r.Close()
	_, st, rents, err := r.ReadAll()
	if err != nil {
		t.Fatal(err)
	}
	if len(rents) != 1 {
		t.Fatalf("durable entries = %d, want 1", len(rents))
	}
	if got := st.GetCommit(); got != 0 {
		t.Fatalf("durable commit = %d; the commit-only HardState was synced", got)
	}
	t.Logf("after Save(commit=1) returned, the durable commit is still %d", st.GetCommit())
}
