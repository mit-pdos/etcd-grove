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
	"path/filepath"
	"testing"

	"github.com/stretchr/testify/require"
	"go.uber.org/zap/zaptest"

	"go.etcd.io/etcd/server/v3/storage/wal/walpb"
	"go.etcd.io/raft/v3/raftpb"
)

// A write-mode ReadAll at a snapshot with no record in the files it reads returns
// ErrSnapshotNotFound, as read mode does.
func TestReadAllSnapshotNotFound(t *testing.T) {
	dir := filepath.Join(t.TempDir(), "w")
	lg := zaptest.NewLogger(t)
	w, err := Create(lg, dir, []byte("md"))
	require.NoError(t, err)
	for i := uint64(1); i <= 5; i++ {
		require.NoError(t, w.Save(&raftpb.HardState{Term: new(uint64(1)), Commit: new(i)}, []*raftpb.Entry{{Index: new(i), Term: new(uint64(1))}}))
	}
	require.NoError(t, w.Close())
	w, err = Open(lg, dir, &walpb.Snapshot{Index: new(uint64(3)), Term: new(uint64(1))})
	require.NoError(t, err)
	defer w.Close()
	_, _, _, err = w.ReadAll()
	require.ErrorIs(t, err, ErrSnapshotNotFound)
}

// ValidSnapshotEntries lists every snapshot record of the directory, but Open reads from the last
// file named at or below the snapshot's index. An entry saved below a snapshot after its record (a
// follower re-saving entries a leader re-sent) used to name the next segment below the snapshot's
// index, so Open at that (valid) snapshot started after its record. A cut now names its segment
// above every snapshot record saved or read, so Open starts at or before the record and ReadAll
// matches it.
func TestReadAllStartRecordBeforeOpenedFile(t *testing.T) {
	old := SegmentSizeBytes
	SegmentSizeBytes = 64 * 1000 * 1000
	defer func() { SegmentSizeBytes = old }()
	dir := filepath.Join(t.TempDir(), "w")
	lg := zaptest.NewLogger(t)
	w, err := Create(lg, dir, []byte("md"))
	require.NoError(t, err)
	cs := &raftpb.ConfState{Voters: []uint64{1}}
	ent := func(i uint64) *raftpb.Entry { return &raftpb.Entry{Term: new(uint64(1)), Index: new(i)} }
	hs := func(c uint64) *raftpb.HardState { return &raftpb.HardState{Term: new(uint64(1)), Commit: new(c)} }
	require.NoError(t, w.Save(hs(5), []*raftpb.Entry{ent(1), ent(2), ent(3), ent(4), ent(5)}))
	require.NoError(t, w.SaveSnapshot(&walpb.Snapshot{Index: new(uint64(5)), Term: new(uint64(1)), ConfState: cs}))
	SegmentSizeBytes = 1
	require.NoError(t, w.Save(hs(5), []*raftpb.Entry{ent(3)})) // the cut names the next segment 6, not 4
	SegmentSizeBytes = 64 * 1000 * 1000
	require.NoError(t, w.Close())

	snaps, err := ValidSnapshotEntries(lg, dir)
	require.NoError(t, err)
	require.Equal(t, uint64(5), snaps[len(snaps)-1].GetIndex())
	w, err = Open(lg, dir, &walpb.Snapshot{Index: new(uint64(5)), Term: new(uint64(1))})
	require.NoError(t, err)
	defer w.Close()
	require.Equal(t, walName(1, 6), filepath.Base(w.tail().Name()))
	require.Len(t, w.locks, 2) // Open starts at the first segment, which holds the record of 5
	_, st, ents, err := w.ReadAll()
	require.NoError(t, err)
	require.Equal(t, uint64(5), st.GetCommit())
	require.Empty(t, ents)
	require.Equal(t, uint64(3), w.enti) // the last entry read
	require.Equal(t, uint64(5), w.snapi)
}
