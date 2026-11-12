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

// A follower persists a received snapshot (41, above its commit 36) and crashes before saving the
// hard state that commits it. It restarts at the older snapshot 0; the leader re-sends entries
// 37..41, which are saved after the record of 41, and a segment is cut between them. Once the commit
// reaches 41, the next restart is at 41. The cut must name its segment above 41 (the snapshot record
// read before it), so that Open at 41 starts at the segment holding the record and the restart
// succeeds. Before, the segment was named 39 (the last entry, 38, plus one): Open at 41 started
// there, after the record, and ReadAll failed with ErrSnapshotNotFound.
func TestRestartAtSnapshotSavedBeforeReSentEntries(t *testing.T) {
	old := SegmentSizeBytes
	SegmentSizeBytes = 64 * 1000 * 1000
	defer func() { SegmentSizeBytes = old }()
	dir := filepath.Join(t.TempDir(), "w")
	lg := zaptest.NewLogger(t)
	w, err := Create(lg, dir, []byte("md"))
	require.NoError(t, err)
	ents := func(lo, hi uint64) []*raftpb.Entry {
		var es []*raftpb.Entry
		for i := lo; i <= hi; i++ {
			es = append(es, &raftpb.Entry{Term: new(uint64(1)), Index: new(i)})
		}
		return es
	}
	hs := func(c uint64) *raftpb.HardState { return &raftpb.HardState{Term: new(uint64(1)), Commit: new(c)} }
	require.NoError(t, w.Save(hs(36), ents(1, 36)))
	require.NoError(t, w.SaveSnapshot(&walpb.Snapshot{Index: new(uint64(41)), Term: new(uint64(1)), ConfState: &raftpb.ConfState{Voters: []uint64{1}}}))
	require.NoError(t, w.Close()) // the crash before the hard state committing 41

	snaps, err := ValidSnapshotEntries(lg, dir)
	require.NoError(t, err)
	require.Equal(t, uint64(0), snaps[len(snaps)-1].GetIndex())
	w, err = Open(lg, dir, &walpb.Snapshot{Index: new(uint64(0)), Term: new(uint64(0))})
	require.NoError(t, err)
	_, _, rents, err := w.ReadAll()
	require.NoError(t, err)
	require.Len(t, rents, 36)
	SegmentSizeBytes = 1
	require.NoError(t, w.Save(hs(36), ents(37, 38))) // cuts a segment
	SegmentSizeBytes = 64 * 1000 * 1000
	require.NoError(t, w.Save(hs(41), ents(39, 41)))
	require.NoError(t, w.Close())
	names, err := readWALNames(lg, dir)
	require.NoError(t, err)
	require.Equal(t, []string{walName(0, 0), walName(1, 42)}, names)

	snaps, err = ValidSnapshotEntries(lg, dir)
	require.NoError(t, err)
	require.Equal(t, uint64(41), snaps[len(snaps)-1].GetIndex())
	w, err = Open(lg, dir, &walpb.Snapshot{Index: new(uint64(41)), Term: new(uint64(1))})
	require.NoError(t, err)
	defer w.Close()
	require.Len(t, w.locks, 2) // Open starts at the segment holding the record of 41
	_, st, rents, err := w.ReadAll()
	require.NoError(t, err)
	require.Equal(t, uint64(41), st.GetCommit())
	require.Empty(t, rents)
	require.Equal(t, uint64(41), w.snapi)
}
