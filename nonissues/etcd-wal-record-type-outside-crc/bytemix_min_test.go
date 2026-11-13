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
	"testing"

	"github.com/stretchr/testify/require"

	"go.etcd.io/raft/v3/raftpb"
)

// The minimized mixes TestWALByteMix finds. The record's CRC covers its Data only, so a tear of the
// one-byte Type value (frame byte 9) alone passes the decoder with no CRC collision.
//
// TestWALTypeTearStale: the last frame is a state record (the unsynced hard state {1,1,2}); its
// Type byte comes back as the byte under it before the write, here 0x02 (EntryType), as when that
// offset held a stale entry record (upstream: ReadAll's zeroing of the torn tail lost; the fork:
// only under a reused N.tmp's remnant). The restart accepts the hard state's bytes as an entry:
// HardState{term 1, vote 1, commit 2} parses as Entry{Type 1 (ConfChange), Term 1, Index 2}, which
// replaces the synced, committed entry 2 (a normal entry with 40 bytes of data).
//
// TestWALTypeTearZero: the same with the byte under it zero (the fork's case, and the preallocated
// tail): the record has Type 0, the decoder accepts it, ReadAll fails with "unexpected block type
// 0", which is not io.ErrUnexpectedEOF: bootstrap does not repair it and the member cannot restart.
func bmTypeTear(t *testing.T, b byte) bmOutcome {
	old := SegmentSizeBytes
	SegmentSizeBytes = 256 * 1024
	defer func() { SegmentSizeBytes = old }()
	sc := bmScenarios()[0] // entry-n-1-t0: prefix, then Save({1,1,2}, [entry 3 with no data])
	require.Equal(t, "entry-n-1-t0", sc.name)
	nb, size := bmWrite(t, sc.ops)
	recs, ends := bmFrames(t, nb, size)
	last := ends[len(ends)-2] // the last frame: the state record
	require.Equal(t, StateType, recs[len(recs)-1].typ)
	require.Equal(t, byte(0x08), nb[last+8])
	require.Equal(t, byte(StateType), nb[last+9])
	img := append([]byte(nil), nb...)
	img[last+9] = b
	return bmRestartReal(t, img, size)
}

func TestWALTypeTearStale(t *testing.T) {
	o := bmTypeTear(t, byte(EntryType))
	t.Logf("restart: %s %s", o.kind, bmShort(o))
	require.Equal(t, "ok", o.kind)
	e2 := o.ents[1]
	require.Equal(t, uint64(2), e2.GetIndex())
	require.Equal(t, raftpb.EntryConfChange, e2.GetType()) // written: EntryNormal, 40 bytes
	require.Empty(t, e2.GetData())
}

func TestWALTypeTearZero(t *testing.T) {
	o := bmTypeTear(t, 0)
	t.Logf("restart: %s %s", o.kind, o.why)
	require.Equal(t, "fatal", o.kind)
	require.Contains(t, o.why, "unexpected block type 0")
}
