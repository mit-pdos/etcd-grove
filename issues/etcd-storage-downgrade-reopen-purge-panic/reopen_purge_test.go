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
	"fmt"
	"os"
	"path/filepath"
	"testing"
	"time"

	"go.uber.org/zap/zaptest"

	"go.etcd.io/etcd/client/pkg/v3/fileutil"
	"go.etcd.io/etcd/server/v3/etcdserver/api/snap"
	"go.etcd.io/etcd/server/v3/storage/wal"
	"go.etcd.io/raft/v3/raftpb"
)

// TestMinimalEtcdVersionConcurrentWithPurge runs the WAL purge the way
// EtcdServer.purgeFile does (PurgeFileWithDoneNotify, flock on), with a
// short interval, while the storage's MinimalEtcdVersion (called by
// schema.UnsafeMigrate on a storage downgrade) reopens the WAL. The WAL holds
// more locked segments than --max-wals since its last snapshot; the purge
// must never delete one of them.
func TestMinimalEtcdVersionConcurrentWithPurge(t *testing.T) {
	old := wal.SegmentSizeBytes
	wal.SegmentSizeBytes = 512 // a few saves per segment
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

	for i := uint64(1); i <= 200; i++ {
		hs := &raftpb.HardState{Term: new(uint64(1)), Commit: new(i)}
		ents := []*raftpb.Entry{{Term: new(uint64(1)), Index: new(i)}}
		if err := st.Save(hs, ents); err != nil {
			t.Fatal(err)
		}
		if i == 10 { // EtcdServer.snapshot: SaveSnap, then Release
			s := &raftpb.Snapshot{Metadata: &raftpb.SnapshotMetadata{
				Index: new(i), Term: new(uint64(1)), ConfState: &raftpb.ConfState{},
			}}
			if err := st.SaveSnap(s); err != nil {
				t.Fatal(err)
			}
			if err := st.Release(s); err != nil {
				t.Fatal(err)
			}
		}
	}

	const maxWALs = 5 // the default --max-wals
	stop := make(chan struct{})
	donec, errc := fileutil.PurgeFileWithDoneNotify(lg, walDir, "wal", maxWALs, time.Millisecond, stop)
	defer func() { close(stop); <-donec }()

	minimal := func() (err error) {
		defer func() {
			if r := recover(); r != nil {
				err = fmt.Errorf("MinimalEtcdVersion panicked: %v", r)
			}
		}()
		st.MinimalEtcdVersion()
		return nil
	}
	for i := 0; i < 200; i++ {
		if err := minimal(); err != nil {
			t.Fatalf("after %d reopens: %v", i, err)
		}
		select {
		case err := <-errc:
			t.Fatalf("purge: %v", err)
		default:
		}
	}
}
