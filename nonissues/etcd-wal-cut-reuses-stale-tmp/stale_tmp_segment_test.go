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
	"errors"
	"fmt"
	"io"
	"math/rand"
	"os"
	"path/filepath"
	"testing"

	"github.com/stretchr/testify/require"
	"go.uber.org/zap"

	"go.etcd.io/etcd/client/pkg/v3/fileutil"
	"go.etcd.io/etcd/pkg/v3/pbutil"
	"go.etcd.io/etcd/server/v3/storage/wal/walpb"
	"go.etcd.io/raft/v3/raftpb"
)

// staleTmpCase is one run of the scenario: a member is killed (or loses power) in the middle of a
// segment cut, after the cut wrote its headers into 0.tmp and before it renamed the file, so 0.tmp
// keeps those headers (the crc record, the metadata, the hard state oldHS). The member restarts,
// and its first cut reuses 0.tmp: the file pipeline opens it without O_TRUNC, so the new headers
// (with newHS, encoded shorter) are written over the old ones and the old headers' tail stays after
// them. The member is stopped right after the cut, before anything is appended to the new segment
// (a kill or a power loss there leaves the same bytes: the cut synced the headers, nothing else was
// written), and restarts as etcd does: ReadAll, and on io.ErrUnexpectedEOF Repair and ReadAll again.
// extra is appended to the stale 0.tmp after the old headers (see the second test).
func staleTmpCase(t *testing.T, oldHS, newHS *raftpb.HardState, oldPrevCrc uint32, extra []*walpb.Record) (repaired bool, st *raftpb.HardState, ents []*raftpb.Entry, err error) {
	t.Helper()
	old := SegmentSizeBytes
	defer func() { SegmentSizeBytes = old }()
	SegmentSizeBytes = 64 * 1000 * 1000
	lg := zap.NewNop()
	dir := filepath.Join(t.TempDir(), "w")
	md := []byte("metadata")

	ent := func(i uint64) *raftpb.Entry {
		return &raftpb.Entry{Term: new(uint64(1)), Index: new(i), Data: []byte("data")}
	}

	// Incarnation 1: some entries, then the interrupted cut.
	w, err := Create(lg, dir, md)
	require.NoError(t, err)
	require.NoError(t, w.Save(oldHS, []*raftpb.Entry{ent(1), ent(2)}))
	require.NoError(t, w.Close())
	// What the interrupted cut leaves: 0.tmp, preallocated, with the cut's headers written and synced
	// (cut syncs them before the rename).
	f, err := createNewWALFile[*os.File](filepath.Join(dir, "0.tmp"), true)
	require.NoError(t, err)
	require.NoError(t, fileutil.Preallocate(f, SegmentSizeBytes, true))
	enc, err := newFileEncoder(f, oldPrevCrc)
	require.NoError(t, err)
	require.NoError(t, enc.encode(&walpb.Record{Type: new(CrcType), Crc: &oldPrevCrc}))
	require.NoError(t, enc.encode(&walpb.Record{Type: new(MetadataType), Data: md}))
	require.NoError(t, enc.encode(&walpb.Record{Type: new(StateType), Data: mustMarshal(t, oldHS)}))
	for _, r := range extra {
		require.NoError(t, enc.encode(r))
	}
	require.NoError(t, enc.flush())
	require.NoError(t, f.Sync())
	require.NoError(t, f.Close())

	// Incarnation 2: restart, a cut (into the reused 0.tmp), stop.
	w, err = Open(lg, dir, &walpb.Snapshot{Index: new(uint64(0)), Term: new(uint64(0))})
	require.NoError(t, err)
	_, _, _, err = w.ReadAll()
	require.NoError(t, err)
	SegmentSizeBytes = 1 // the next Save cuts
	require.NoError(t, w.Save(newHS, []*raftpb.Entry{ent(3)}))
	SegmentSizeBytes = 64 * 1000 * 1000
	require.NoError(t, w.Close())
	names, err := readWALNames(lg, dir)
	require.NoError(t, err)
	require.Len(t, names, 2)

	// Incarnation 3: restart as etcd's bootstrap does (openWALFromSnapshot).
	for {
		w, err = Open(lg, dir, &walpb.Snapshot{Index: new(uint64(0)), Term: new(uint64(0))})
		require.NoError(t, err)
		_, st, ents, err = w.ReadAll()
		w.Close()
		if err == nil || repaired || !errors.Is(err, io.ErrUnexpectedEOF) {
			return repaired, st, ents, err
		}
		if !Repair(lg, dir) {
			return repaired, st, ents, fmt.Errorf("repair failed after %w", err)
		}
		repaired = true
	}
}

func mustMarshal(t *testing.T, hs *raftpb.HardState) []byte {
	t.Helper()
	return pbutil.MustMarshalMessage(hs)
}

func hsEqual(a, b *raftpb.HardState) bool {
	return a.GetTerm() == b.GetTerm() && a.GetVote() == b.GetVote() && a.GetCommit() == b.GetCommit()
}

// TestRestartAfterCutReusesStaleTmp: the restart reads the new history (the hard state saved last
// and entries 1..3), with or without a repair, for old hard states whose encoding is longer than
// the new one's by 8 to 24 bytes (a vote for a member ID, then a higher term with no vote yet),
// with random member IDs, terms, commits and chain CRCs.
func TestRestartAfterCutReusesStaleTmp(t *testing.T) {
	rnd := rand.New(rand.NewSource(1))
	n := 60
	if testing.Short() {
		n = 10
	}
	shorter, repairs := 0, 0
	for i := 0; i < n; i++ {
		term := uint64(rnd.Intn(1 << uint(1+rnd.Intn(30))))
		oldHS := &raftpb.HardState{Term: new(term), Vote: new(rnd.Uint64() | 1<<uint(rnd.Intn(64))), Commit: new(uint64(rnd.Intn(1 << uint(1+rnd.Intn(40)))))}
		newCommit := oldHS.GetCommit() + uint64(rnd.Intn(3))
		newHS := &raftpb.HardState{Term: new(term + 1), Vote: new(uint64(0)), Commit: new(newCommit)}
		if rnd.Intn(4) == 0 {
			newHS.Vote = nil
		}
		oldLen := len(mustMarshal(t, oldHS))
		newLen := len(mustMarshal(t, newHS))
		if (oldLen+7)/8 > (newLen+7)/8 {
			shorter++
		}
		repaired, st, ents, err := staleTmpCase(t, oldHS, newHS, rnd.Uint32(), nil)
		require.NoError(t, err, "case %d: old %v new %v", i, oldHS, newHS)
		require.True(t, hsEqual(st, newHS), "case %d: read %v, saved %v", i, st, newHS)
		require.Len(t, ents, 3, "case %d", i)
		if repaired {
			repairs++
		}
	}
	t.Logf("%d cases, %d with stale bytes after the new headers, %d repaired", n, shorter, repairs)
	require.Positive(t, shorter)
}

// TestRestartAfterCutReusesStaleTmpWithRecords is a state no crash of etcd leaves: 0.tmp holding
// records after the old headers. A cut appends to its segment only after the rename and the
// directory fsync, so a 0.tmp that a crash leaves never holds more than the headers. If it did,
// the old records after the new headers would not look torn, and the restart would fail: the
// O_TRUNC-less reuse is safe only because of that ordering. Here the old and the new hard states
// encode to the same length, so the new headers end where the old ones did and the next frame is
// an old entry record, which fails the CRC chain without looking torn: ReadAll fails with
// ErrCRCMismatch, which Repair does not handle.
func TestRestartAfterCutReusesStaleTmpWithRecords(t *testing.T) {
	oldHS := &raftpb.HardState{Term: new(uint64(5)), Vote: new(uint64(1)), Commit: new(uint64(10))}
	newHS := &raftpb.HardState{Term: new(uint64(6)), Vote: new(uint64(0)), Commit: new(uint64(10))}
	var extra []*walpb.Record
	for i := uint64(3); i < 10; i++ {
		e := &raftpb.Entry{Term: new(uint64(5)), Index: new(i), Data: []byte("stale entry, never committed")}
		extra = append(extra, &walpb.Record{Type: new(EntryType), Data: pbutil.MustMarshalMessage(e)})
	}
	repaired, _, ents, err := staleTmpCase(t, oldHS, newHS, 0x12345678, extra)
	t.Logf("repaired=%v entries=%d err=%v", repaired, len(ents), err)
	require.ErrorIs(t, err, walpb.ErrCRCMismatch)
}
