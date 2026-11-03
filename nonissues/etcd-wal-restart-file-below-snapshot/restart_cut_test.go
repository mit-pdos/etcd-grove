package walrestart

import (
	"errors"
	"os"
	"strings"
	"testing"
	"time"

	"go.etcd.io/etcd/client/pkg/v3/fileutil"

	"go.uber.org/zap/zaptest"

	"go.etcd.io/etcd/api/v3/etcdserverpb"
	"go.etcd.io/etcd/pkg/v3/pbutil"
	"go.etcd.io/etcd/server/v3/etcdserver/api/snap"
	serverstorage "go.etcd.io/etcd/server/v3/storage"
	"go.etcd.io/etcd/server/v3/storage/wal"
	"go.etcd.io/etcd/server/v3/storage/wal/walpb"
	"go.etcd.io/raft/v3/raftpb"
)

func hs(term, vote, commit uint64) *raftpb.HardState {
	return &raftpb.HardState{Term: new(term), Vote: new(vote), Commit: new(commit)}
}

func ents(term, from, to uint64) []*raftpb.Entry {
	var es []*raftpb.Entry
	for i := from; i <= to; i++ {
		es = append(es, &raftpb.Entry{Index: new(i), Term: new(term)})
	}
	return es
}

func snapAt(index, term uint64) *raftpb.Snapshot {
	return &raftpb.Snapshot{Metadata: &raftpb.SnapshotMetadata{
		Index: new(index), Term: new(term), ConfState: &raftpb.ConfState{Voters: []uint64{1}},
	}}
}

func meta() []byte {
	return pbutil.MustMarshalMessage(&etcdserverpb.Metadata{NodeID: new(uint64(1)), ClusterID: new(uint64(7))})
}

// create is bootstrapNewWAL: wal.Create, wrapped in the server's Storage.
func create(t *testing.T, dir string) (*wal.WAL, serverstorage.Storage) {
	w, err := wal.Create(zaptest.NewLogger(t), dir, meta())
	if err != nil {
		t.Fatal(err)
	}
	return w, serverstorage.NewStorage(zaptest.NewLogger(t), w, snap.New(zaptest.NewLogger(t), t.TempDir()))
}

// reopen is the restart's bootstrap: recoverSnapshot (ValidSnapshotEntries, the record of the
// highest index, the last among equals: newestSnapshotEntry) and openWALFromSnapshot (Open, ReadAll).
func reopen(t *testing.T, dir string) (*wal.WAL, *walpb.Snapshot, *raftpb.HardState, []*raftpb.Entry, error) {
	walSnaps, err := wal.ValidSnapshotEntries(zaptest.NewLogger(t), dir)
	if err != nil {
		t.Fatal(err)
	}
	ws := &walpb.Snapshot{}
	if len(walSnaps) > 0 {
		idx := 0
		for i, s := range walSnaps {
			if s.GetIndex() >= walSnaps[idx].GetIndex() {
				idx = i
			}
		}
		ws = &walpb.Snapshot{Index: new(walSnaps[idx].GetIndex()), Term: new(walSnaps[idx].GetTerm())}
	}
	w, err := wal.Open(zaptest.NewLogger(t), dir, ws)
	if err != nil {
		// openWALFromSnapshot: cfg.Logger.Fatal("failed to open WAL", ...)
		return nil, ws, nil, nil, err
	}
	_, st, es, err := w.ReadAll()
	return w, ws, st, es, err
}

func ids(es []*raftpb.Entry) [][2]uint64 {
	var r [][2]uint64
	for _, e := range es {
		r = append(r, [2]uint64{e.GetIndex(), e.GetTerm()})
	}
	return r
}

// A1 (server order). A follower with entries 1..3 receives a snapshot at 5 (the raft loop:
// SaveSnap, Save of the hard state at commit 5, Release), stops (Close) and restarts: the records
// are base 5, no entries. After the restart its first batch is a hard state only (a vote) that
// fills the segment, so Save cuts the file. The cut names the new file by w.enti+1, and ReadAll
// set w.enti from the entry records only (3), not from the start snapshot (5): the new file is
// named 1-4. It stops (Close), with records base 5, no entries, by walSave; the next restart opens
// at the record 5, searchIndex picks the file 1-4, which does not hold it: ErrSnapshotNotFound.
func TestA1RestartAfterReceivedSnapshotThenCut(t *testing.T) {
	dir := t.TempDir() + "/wal"
	w, st := create(t, dir)
	must(t, st.Save(hs(1, 0, 1), ents(1, 1, 3)))
	m := snapAt(5, 2)
	must(t, st.SaveSnap(m))
	must(t, st.Save(hs(2, 0, 5), nil))
	must(t, st.Sync())
	must(t, st.Release(m))
	must(t, st.Close())
	_ = w

	w2, ws, h, es, err := reopen(t, dir)
	must(t, err)
	t.Logf("restart 1: start %d/%d hs commit %d ents %v", ws.GetIndex(), ws.GetTerm(), h.GetCommit(), ids(es))
	st2 := serverstorage.NewStorage(zaptest.NewLogger(t), w2, snap.New(zaptest.NewLogger(t), t.TempDir()))

	old := wal.SegmentSizeBytes
	wal.SegmentSizeBytes = 1 // stand-in for a tail file that reached 64 MB
	must(t, st2.Save(hs(3, 2, 5), nil))
	wal.SegmentSizeBytes = old
	must(t, st2.Close())

	w3, ws, h, es, err := reopen(t, dir)
	if err != nil {
		t.Fatalf("restart 2 (start %d/%d): ReadAll: %v (the model: base 5, hard state 3/2/5, no entries)", ws.GetIndex(), ws.GetTerm(), err)
	}
	defer w3.Close()
	t.Logf("restart 2: start %d hs %v ents %v", ws.GetIndex(), h, ids(es))
}



func must(t *testing.T, err error) {
	t.Helper()
	if err != nil {
		t.Fatal(err)
	}
}

// A4 (server order). As A1: a follower with entries 1..3 receives a snapshot at 5 (SaveSnap,
// Save at commit 5), stops and restarts (records: base 5, no entries; ReadAll leaves w.enti at 3).
// Its next batches are hard states only (votes in new terms) that fill segments: each cut names
// its file by w.enti+1 = 4. It stops (Close: records base 5, hard state 3+k/2/5, no entries) and
// restarts: the start file is now the last one named at or below 5, a file after the record 5,
// so the file holding it (0-0) is no longer locked, and the server's purge goroutine
// (PurgeFileWithDoneNotify(WALDir, "wal", MaxWALFiles = 5)) deletes it. The member stops again
// (Close, the same records) and restarts: ValidSnapshotEntries finds no snapshot record,
// recoverSnapshot starts from scratch, and wal.Open at index 0 fails (no file named at or below
// 0): openWALFromSnapshot calls lg.Fatal. The model: walFiles of base 5, hard state, no entries.
func TestA4ReceivedSnapshotRestartCutsPurgeRestart(t *testing.T) {
	dir := t.TempDir() + "/wal"
	_, st := create(t, dir)
	must(t, st.Save(hs(1, 0, 1), ents(1, 1, 3)))
	m := snapAt(5, 2)
	must(t, st.SaveSnap(m))
	must(t, st.Save(hs(2, 0, 5), nil))
	must(t, st.Sync())
	must(t, st.Release(m))
	must(t, st.Close())

	w2, _, _, _, err := reopen(t, dir)
	must(t, err)
	st2 := serverstorage.NewStorage(zaptest.NewLogger(t), w2, snap.New(zaptest.NewLogger(t), t.TempDir()))
	old := wal.SegmentSizeBytes
	wal.SegmentSizeBytes = 1 // stand-in: each hard-state-only Save fills a 64 MB segment
	for k := uint64(0); k < 5; k++ {
		must(t, st2.Save(hs(3+k, 2, 5), nil))
	}
	wal.SegmentSizeBytes = old
	must(t, st2.Close())
	t.Logf("files after restart 1: %v", walNames(t, dir))

	w3, ws, h, es, err := reopen(t, dir)
	must(t, err)
	t.Logf("restart 2: start %d/%d, hs %v, ents %v", ws.GetIndex(), ws.GetTerm(), h, ids(es))
	// the server's WAL purge (NewServer's purgeFile, MaxWALFiles = 5 by default)
	stop := make(chan struct{})
	donec, _ := fileutil.PurgeFileWithDoneNotify(zaptest.NewLogger(t), dir, "wal", 5, time.Hour, stop)
	for i := 0; i < 100 && len(walNames(t, dir)) > 5; i++ {
		time.Sleep(10 * time.Millisecond)
	}
	close(stop)
	<-donec
	must(t, w3.Close())
	t.Logf("files after restart 2 and the purge: %v", walNames(t, dir))

	w4, ws, h, es, err := reopen(t, dir)
	if err != nil {
		t.Fatalf("restart 3 (start %d/%d): %v; the model's records: base 5/2, hard state 7/2/5, no entries", ws.GetIndex(), ws.GetTerm(), err)
	}
	defer w4.Close()
	if ws.GetIndex() != 5 || h.GetCommit() != 5 || len(es) != 0 {
		t.Fatalf("restart 3: start %d/%d, hs %v, ents %v; the model's: base 5/2, hard state 7/2/5, no entries", ws.GetIndex(), ws.GetTerm(), h, ids(es))
	}
}

func walNames(t *testing.T, dir string) []string {
	des, err := os.ReadDir(dir)
	must(t, err)
	var r []string
	for _, d := range des {
		if strings.HasSuffix(d.Name(), ".wal") {
			r = append(r, d.Name())
		}
	}
	return r
}
