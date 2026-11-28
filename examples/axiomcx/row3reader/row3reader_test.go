// Package row3reader is the Go evidence for notes/axiom-review/row3-reader-packet.md: bootstrap's
// restart contract (bootstrapRestartContract, wal.restartOk) stated over the READER (walRead Hs = some σ,
// Hs the files' history) instead of the eager fold (walFoldChkFrom walFresh Hs = some σ). At the etcd pin
// (examples/go.mod).
//
// The crash is a real one: a child process (this test binary, re-run with ROW3_PHASE set) writes the
// records and dies with os.Exit, without Close, right after the synced call, as a kill would leave it.
//
// TestSnapBeforeSaveCrash: Save(commit 5, entries 1..5), SaveSnapshot(3), then raftNode's order for a
// received snapshot (raft.go:266-291): SaveSnap(10) (synced, wal.go:1423), and the process dies before
// Save(hs{commit 10}). The reader (ValidSnapshotEntries + Open + ReadAll, what bootstrap runs) gives
// base 3, commit 5, entries [4 5]: walRead's σ (walKeep drops the record at 10 > commit 5). The eager
// fold would give base 10 and no entries.
//
// TestDanglingSnapRevived (what the downstream restart proof must model): the restarted member (raft at
// base 3, commit 5) appends entries 6..12 at commit 12 and dies again. The reader now keeps the record at
// 10 (10 <= 12): base 10, commit 12, entries [11 12]. So a dangling snapshot record is not gone: a later
// commit revives it (walReadAt Hs c for c >= 10), which the crash invariant's HistReads must allow.
//
// Run: cd examples && go test ./axiomcx/row3reader/ -v
package row3reader

import (
	"os"
	"os/exec"
	"path/filepath"
	"testing"

	"go.etcd.io/etcd/server/v3/storage/wal"
	"go.etcd.io/etcd/server/v3/storage/wal/walpb"
	"go.etcd.io/raft/v3/raftpb"
	"go.uber.org/zap"
)

func u(x uint64) *uint64 { return &x }

func ents(lo, hi uint64) []*raftpb.Entry {
	var es []*raftpb.Entry
	for i := lo; i <= hi; i++ {
		es = append(es, &raftpb.Entry{Index: u(i), Term: u(1)})
	}
	return es
}

func snap(i uint64) *walpb.Snapshot {
	return &walpb.Snapshot{Index: u(i), Term: u(1), ConfState: &raftpb.ConfState{}}
}

func must(err error) {
	if err != nil {
		panic(err)
	}
}

// The child: run one phase's writes, then die without Close.
func TestMain(m *testing.M) {
	lg := zap.NewNop()
	wd := os.Getenv("ROW3_DIR")
	switch os.Getenv("ROW3_PHASE") {
	case "1":
		w, err := wal.Create(lg, wd, []byte("md"))
		must(err)
		must(w.Save(&raftpb.HardState{Term: u(1), Commit: u(5)}, ents(1, 5)))
		must(w.SaveSnapshot(snap(3)))
		must(w.SaveSnapshot(snap(10))) // the received snapshot's SaveSnap: synced
		os.Exit(0)                     // killed before Save(hs{commit 10})
	case "2":
		// the restart, as bootstrap opens it: the newest valid snapshot, ReadAll (write mode)
		ss, err := wal.ValidSnapshotEntries(lg, wd)
		must(err)
		w, err := wal.Open(lg, wd, ss[len(ss)-1])
		must(err)
		_, _, _, err = w.ReadAll()
		must(err)
		// raft restarted at base 3, commit 5: the leader sends 6..12, committed at 12
		must(w.Save(&raftpb.HardState{Term: u(1), Commit: u(12)}, ents(6, 12))) // MustSync: synced
		os.Exit(0)
	}
	os.Exit(m.Run())
}

func child(t *testing.T, wd, phase string) {
	cmd := exec.Command(os.Args[0])
	cmd.Env = append(os.Environ(), "ROW3_DIR="+wd, "ROW3_PHASE="+phase)
	if out, err := cmd.CombinedOutput(); err != nil {
		t.Fatalf("phase %s: %v\n%s", phase, err, out)
	}
}

// read runs bootstrap's WAL read (read-only open, as a check) and returns the newest valid snapshot
// index, the commit and the entries' indices.
func read(t *testing.T, wd string) (uint64, uint64, []uint64) {
	lg := zap.NewNop()
	ss, err := wal.ValidSnapshotEntries(lg, wd)
	if err != nil {
		t.Fatal(err)
	}
	newest := ss[len(ss)-1]
	w, err := wal.OpenForRead(lg, wd, newest)
	if err != nil {
		t.Fatal(err)
	}
	defer w.Close()
	_, st, es, err := w.ReadAll()
	if err != nil {
		t.Fatalf("ReadAll: %v", err)
	}
	var idx []uint64
	for _, e := range es {
		idx = append(idx, e.GetIndex())
	}
	return newest.GetIndex(), st.GetCommit(), idx
}

func eq(a, b []uint64) bool {
	if len(a) != len(b) {
		return false
	}
	for i := range a {
		if a[i] != b[i] {
			return false
		}
	}
	return true
}

func TestSnapBeforeSaveCrash(t *testing.T) {
	wd := filepath.Join(t.TempDir(), "wal")
	child(t, wd, "1")
	b, c, es := read(t, wd)
	t.Logf("reader: base %d commit %d entries %v (eager fold: base 10, no entries)", b, c, es)
	if b != 3 || c != 5 || !eq(es, []uint64{4, 5}) {
		t.Fatalf("reader differs from walRead's sigma (base 3, commit 5, [4 5])")
	}
}

func TestDanglingSnapRevived(t *testing.T) {
	wd := filepath.Join(t.TempDir(), "wal")
	child(t, wd, "1")
	child(t, wd, "2")
	b, c, es := read(t, wd)
	t.Logf("reader after the restarted Save(commit 12, 6..12): base %d commit %d entries %v", b, c, es)
	if b != 10 || c != 12 || !eq(es, []uint64{11, 12}) {
		t.Fatalf("expected the dangling record at 10 revived: base 10, commit 12, [11 12]")
	}
}
