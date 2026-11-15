// A follower is killed while persisting a raft Ready that holds a snapshot received from the
// leader and entries after it: raftNode calls SaveSnap, then Save(hardState, entries); the kill
// comes after Save's entries reached the file (they exceed the 128 KiB write buffer) and before
// its hard state did. The member must restart from what the kill left.
package wal_test

import (
	"encoding/binary"
	"errors"
	"os"
	"path/filepath"
	"testing"

	"go.etcd.io/etcd/server/v3/storage/wal"
	"go.etcd.io/etcd/server/v3/storage/wal/walpb"
	"go.etcd.io/raft/v3/raftpb"
	"go.uber.org/zap"
)

func cw1U64(x uint64) *uint64 { return &x }

func cw1Ents(lo, hi, term uint64, size int) []*raftpb.Entry {
	var es []*raftpb.Entry
	for i := lo; i <= hi; i++ {
		d := make([]byte, size)
		for j := range d {
			d[j] = byte(1 + (int(i)+j)%251)
		}
		es = append(es, &raftpb.Entry{Index: cw1U64(i), Term: cw1U64(term), Type: raftpb.EntryType_EntryNormal.Enum(), Data: d})
	}
	return es
}

// cw1Frames returns the end offsets of the records of a WAL file.
func cw1Frames(b []byte) []int {
	var ends []int
	off := 0
	for off+8 <= len(b) {
		l := int64(binary.LittleEndian.Uint64(b[off:]))
		if l == 0 {
			break
		}
		rec := int(uint64(l) & ^(uint64(0xff) << 56))
		pad := 0
		if l < 0 {
			pad = int((uint64(l) >> 56) & 0x7)
		}
		off += 8 + rec + pad
		ends = append(ends, off)
	}
	return ends
}

func TestReceivedSnapshotSaveCrashBlocksRestart(t *testing.T) {
	lg := zap.NewNop()
	dir := filepath.Join(t.TempDir(), "wal")
	w, err := wal.Create(lg, dir, []byte("m"))
	if err != nil {
		t.Fatal(err)
	}
	// the follower's log: 1..3 committed
	if err := w.Save(&raftpb.HardState{Term: cw1U64(1), Vote: cw1U64(1), Commit: cw1U64(3)}, cw1Ents(1, 3, 1, 100)); err != nil {
		t.Fatal(err)
	}
	// raftNode: a Ready with a snapshot (10) and entries 11..12 above it: SaveSnap, then Save
	if err := w.SaveSnapshot(&walpb.Snapshot{Index: cw1U64(10), Term: cw1U64(2), ConfState: &raftpb.ConfState{Voters: []uint64{1, 2, 3}}}); err != nil {
		t.Fatal(err)
	}
	if err := w.Save(&raftpb.HardState{Term: cw1U64(2), Commit: cw1U64(12)}, cw1Ents(11, 12, 2, 100<<10)); err != nil {
		t.Fatal(err)
	}
	w.Close()
	// the kill -9 image: the 200 KiB of entries passed the 128 KiB page writer and reached the
	// file; the state record, encoded after them, stayed in the buffer
	p := filepath.Join(dir, "0000000000000000-0000000000000000.wal")
	b, _ := os.ReadFile(p)
	fr := cw1Frames(b)
	if err := os.Truncate(p, int64(fr[len(fr)-2])); err != nil { // drop the last record (the state)
		t.Fatal(err)
	}
	if err := os.Truncate(p, int64(len(b))); err != nil { // the preallocated size back
		t.Fatal(err)
	}
	// bootstrap's restart: newest valid snapshot record, Open, ReadAll
	snaps, err := wal.ValidSnapshotEntries(lg, dir)
	if err != nil {
		t.Fatal(err)
	}
	start := snaps[len(snaps)-1]
	w2, err := wal.Open(lg, dir, &walpb.Snapshot{Index: cw1U64(start.GetIndex()), Term: cw1U64(start.GetTerm())})
	if err != nil {
		t.Fatal(err)
	}
	defer w2.Close()
	_, _, _, err = w2.ReadAll()
	if errors.Is(err, wal.ErrSliceOutOfRange) {
		t.Fatalf("restart after a crash in the Save following a received snapshot fails (bootstrap Fatals): open at snapshot %d: %v", start.GetIndex(), err)
	}
}
