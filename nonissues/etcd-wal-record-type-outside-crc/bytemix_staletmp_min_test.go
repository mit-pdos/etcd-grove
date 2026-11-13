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
	"bytes"
	"math/rand"
	"slices"
	"testing"

	"github.com/stretchr/testify/require"
	"google.golang.org/protobuf/proto"

	"go.etcd.io/etcd/pkg/v3/pbutil"
	"go.etcd.io/etcd/server/v3/storage/wal/walpb"
	"go.etcd.io/raft/v3/raftpb"
)

// TestWALTypeTearStaleTmp: the fork's own case of TestWALTypeTearStale. After an interrupted cut
// and a restart, the next cut writes its headers over the reused 0.tmp
// (nonissues/etcd-wal-cut-reuses-stale-tmp). Were 0.tmp reused as it was, the stale remnant of the
// old hard-state frame would stay after the new headers, and the first Save after the cut would
// append an entry record over it. When the remnant's byte under the entry frame's Type value is 3
// (StateType) or 5 (SnapshotType), a power loss that keeps every byte of the Save but that one
// would make the restart read the entry's bytes as a hard state (or a snapshot record), with a
// valid CRC. The test searches hard states (a vote for a member ID, a commit) whose old frame puts
// such a byte there, and runs the restart on that image: it must fail or read only records the WAL
// wrote there. (The pipeline truncates N.tmp: the byte under the Type is 0 and ReadAll fails.)
func TestWALTypeTearStaleTmp(t *testing.T) {
	rnd := rand.New(rand.NewSource(3))
	frameLen := func(data []byte, crcv uint32) int {
		n := proto.Size(&walpb.Record{Type: new(StateType), Crc: new(crcv), Data: data})
		return 8 + (n+7)/8*8
	}
	found, cands, shifted := 0, 0, 0
	for try := 0; try < 2000000 && found < 3 && cands < 3000; try++ {
		term := uint64(1 + rnd.Intn(1<<uint(1+rnd.Intn(20))))
		commit := uint64(rnd.Intn(1 << uint(1+rnd.Intn(30))))
		if try%2 == 0 {
			commit = uint64(3 + 2*rnd.Intn(2)) // a last byte 3 or 5
		}
		oldHS := &raftpb.HardState{Term: new(term), Vote: new(rnd.Uint64() | 1<<63), Commit: new(commit)}
		newHS := &raftpb.HardState{Term: new(term + 1), Vote: new(uint64(0)), Commit: new(oldHS.GetCommit())}
		prev := rnd.Uint32()
		var buf bytes.Buffer
		enc := newEncoder(&buf, prev, 0)
		require.NoError(t, enc.encode(&walpb.Record{Type: new(CrcType), Crc: &prev}))
		require.NoError(t, enc.encode(&walpb.Record{Type: new(MetadataType), Data: []byte("metadata")}))
		require.NoError(t, enc.flush())
		hsStart := buf.Len()
		require.NoError(t, enc.encode(&walpb.Record{Type: new(StateType), Data: pbutil.MustMarshalMessage(oldHS)}))
		require.NoError(t, enc.flush())
		old := buf.Bytes()
		// the new headers' CRC field encodes in 4 or 5 bytes (unknown before the run)
		var poss []int
		for _, crcv := range []uint32{1 << 31, 1 << 22} {
			p := hsStart + frameLen(pbutil.MustMarshalMessage(newHS), crcv) + 9 // the first appended frame's Type
			if p < len(old) && (old[p] == byte(StateType) || old[p] == byte(SnapshotType)) {
				poss = append(poss, p)
			}
		}
		if len(poss) == 0 {
			continue
		}
		cands++
		saveHS := &raftpb.HardState{Term: new(term + 1), Vote: new(uint64(2)), Commit: new(oldHS.GetCommit())}
		ents := []*raftpb.Entry{{Term: new(term + 1), Index: new(uint64(4)), Type: new(raftpb.EntryNormal), Data: []byte("an entry")}}
		seg0, before, after, size := bmStaleTmp(t, oldHS, newHS, saveHS, prev, ents)
		written, ends, _ := bmDecode(after, size, seg0)
		s := ends[len(ends)-3] // the entry frame (then the state frame)
		if !slices.Contains(poss, int(s)+9) {
			shifted++
			continue // the new headers' CRC encoded otherwise than assumed
		}
		found++
		img := append([]byte(nil), after...)
		img[s+9] = before[s+9] // one byte: the Type value as it was before the Save
		o := bmRestartMem(img, size, seg0)
		t.Logf("old %v new %v: entry Type byte %#x -> %#x: %s %s %s", oldHS, newHS, after[s+9], before[s+9], o.kind, o.why, bmShort(o))
		if o.kind != "ok" {
			continue // a failed restart is allowed
		}
		prefix := len(o.recs) <= len(written)
		for j := 0; prefix && j < len(o.recs); j++ {
			prefix = o.recs[j].eq(written[j])
		}
		require.True(t, prefix, "the restart reads records the WAL never wrote there")
	}
	t.Logf("candidates %d, shifted %d, found %d", cands, shifted, found)
	require.Positive(t, found)
}
