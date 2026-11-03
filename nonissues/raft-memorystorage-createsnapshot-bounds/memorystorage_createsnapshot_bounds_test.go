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

package raft

import (
	"testing"

	"github.com/stretchr/testify/require"

	pb "go.etcd.io/raft/v3/raftpb"
)

func createSnapshotBoundsEnts(n uint64) []*pb.Entry {
	ents := make([]*pb.Entry, 0, n)
	for i := uint64(1); i <= n; i++ {
		ents = append(ents, &pb.Entry{Index: new(i), Term: new(uint64(1))})
	}
	return ents
}

// TestMemoryStorageCreateSnapshotBelowCompaction: CreateSnapshot at an index
// the storage has compacted (but newer than its snapshot, since Compact does not
// move the snapshot) indexes ms.ents with a wrapped-around offset and panics
// with "index out of range", where Term and Entries return ErrCompacted.
func TestMemoryStorageCreateSnapshotBelowCompaction(t *testing.T) {
	ms := NewMemoryStorage()
	require.NoError(t, ms.Append(createSnapshotBoundsEnts(5)))
	require.NoError(t, ms.Compact(4))
	require.NotPanics(t, func() {
		_, err := ms.CreateSnapshot(2, nil, nil)
		require.ErrorIs(t, err, ErrCompacted)
	})
}

// TestMemoryStorageCreateSnapshotPastLastIndex: CreateSnapshot past the last
// index panics ("snapshot 2 is out of bound lastindex(1)"); its documentation
// states no range.
func TestMemoryStorageCreateSnapshotPastLastIndex(t *testing.T) {
	ms := NewMemoryStorage()
	require.NoError(t, ms.Append(createSnapshotBoundsEnts(1)))
	require.NotPanics(t, func() {
		_, _ = ms.CreateSnapshot(2, nil, nil)
	})
}
