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

package storage

import (
	"os"
	"path/filepath"
	"sync"
	"testing"

	"go.uber.org/zap/zaptest"

	"go.etcd.io/etcd/server/v3/etcdserver/api/snap"
	"go.etcd.io/etcd/server/v3/storage/wal"
	"go.etcd.io/raft/v3/raftpb"
)

// TestStorageSyncConcurrentWithRelease drives the Storage the way the
// etcdserver does on a follower that receives a snapshot while its apply
// goroutine takes one: the raft goroutine calls Save and then Sync
// (raft.go, "Force WAL to fsync its hard state before Release()"), while the
// apply goroutine calls SaveSnap and Release (EtcdServer.snapshot). Both hold
// only the storage's read lock, so the two must be safe to run concurrently.
func TestStorageSyncConcurrentWithRelease(t *testing.T) {
	old := wal.SegmentSizeBytes
	wal.SegmentSizeBytes = 4 * 1024 // a few entries per segment, so Save cuts segments
	defer func() { wal.SegmentSizeBytes = old }()

	lg := zaptest.NewLogger(t)
	dir := t.TempDir()
	walDir, snapDir := filepath.Join(dir, "wal"), filepath.Join(dir, "snap")
	if err := os.Mkdir(snapDir, 0o700); err != nil {
		t.Fatal(err)
	}
	w, err := wal.Create(lg, walDir, nil)
	if err != nil {
		t.Fatal(err)
	}
	st := NewStorage(lg, w, snap.New(lg, snapDir))
	defer st.Close()

	const n = 200
	data := make([]byte, 1024)
	save := func(i uint64) {
		hs := &raftpb.HardState{Term: new(uint64(1)), Commit: new(i)}
		ents := []*raftpb.Entry{{Term: new(uint64(1)), Index: new(i), Data: data}}
		if err := st.Save(hs, ents); err != nil {
			t.Error(err)
		}
	}
	for i := uint64(1); i <= 20; i++ {
		save(i)
	}

	var wg sync.WaitGroup
	wg.Add(2)
	go func() { // the raft goroutine
		defer wg.Done()
		for i := uint64(21); i <= n; i++ {
			save(i)
			if err := st.Sync(); err != nil {
				t.Error(err)
			}
		}
	}()
	go func() { // the apply goroutine
		defer wg.Done()
		for i := uint64(5); i <= 20; i++ {
			s := &raftpb.Snapshot{Metadata: &raftpb.SnapshotMetadata{
				Index: new(i), Term: new(uint64(1)), ConfState: &raftpb.ConfState{},
			}}
			if err := st.SaveSnap(s); err != nil {
				t.Error(err)
			}
			if err := st.Release(s); err != nil {
				t.Error(err)
			}
		}
	}()
	wg.Wait()
}
