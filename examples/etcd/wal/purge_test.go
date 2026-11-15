package wal

// Go evidence for purgeRound's trust-boundary axiom (WAL W4c, the purgeRound Freeze;
// Spec/github_com/mit_pdos/etcd_grove/examples/etcd/wal/purgeRound.lean): while the WAL is open,
// a round deletes only whole files before the first one the WAL keeps locked (the files from the
// one holding the unlock position unl on: Open's and ReleaseLockTo's), oldest first, stopping at
// the first file it cannot lock; so a graceful restart reads what it read before. Without an open
// handle nothing is locked and the round deletes the file holding the newest snapshot record,
// which is why the axiom takes walOpenW and walPurgeW.
//
//	go test ./etcd/wal -run TestPurgeRound -v

import (
	"fmt"
	"os"
	"path/filepath"
	"sort"
	"strings"
	"testing"

	"go.uber.org/zap"

	"go.etcd.io/etcd/client/pkg/v3/fileutil"
	etcdwal "go.etcd.io/etcd/server/v3/storage/wal"
	"go.etcd.io/etcd/server/v3/storage/wal/walpb"
	"go.etcd.io/raft/v3/raftpb"
)

const purgeTerm = 2

// purgeSeg sets a small segment size for the test (cuts every few entries).
func purgeSeg(t *testing.T) {
	old := etcdwal.SegmentSizeBytes
	etcdwal.SegmentSizeBytes = 4096
	t.Cleanup(func() { etcdwal.SegmentSizeBytes = old })
}

// walFiles lists dir's WAL files (the names ending in "wal"), sorted.
func walFiles(t *testing.T, dir string) []string {
	t.Helper()
	ns, err := os.ReadDir(dir)
	if err != nil {
		t.Fatal(err)
	}
	var out []string
	for _, n := range ns {
		if strings.HasSuffix(n.Name(), "wal") {
			out = append(out, n.Name())
		}
	}
	sort.Strings(out)
	return out
}

// fileIndex is the index in a WAL file's name (seq-index.wal).
func fileIndex(t *testing.T, name string) uint64 {
	t.Helper()
	var seq, idx uint64
	if _, err := fmt.Sscanf(name, "%016x-%016x.wal", &seq, &idx); err != nil {
		t.Fatalf("name %q: %v", name, err)
	}
	return idx
}

func pEnt(i uint64) *raftpb.Entry {
	return toRaft(entry{index: i, term: purgeTerm, size: 1000, salt: i})
}

// saveEnts saves the entries lo..hi, one Save each, with the commit at hi.
func saveEnts(t *testing.T, w *etcdwal.WAL, lo, hi uint64) {
	t.Helper()
	for i := lo; i <= hi; i++ {
		hs := toHS(hardState{term: purgeTerm, vote: 1, commit: i})
		if err := w.Save(hs, []*raftpb.Entry{pEnt(i)}); err != nil {
			t.Fatal(err)
		}
	}
}

func pSnap(i uint64) *walpb.Snapshot {
	return &walpb.Snapshot{Index: newU64(i), Term: newU64(purgeTerm), ConfState: &raftpb.ConfState{Voters: []uint64{1}}}
}

// newPurgeWAL creates a WAL with the entries 1..30, a snapshot record at 20, and the entries
// 31..40 (about ten files).
func newPurgeWAL(t *testing.T) (*zap.Logger, string, *etcdwal.WAL) {
	purgeSeg(t)
	lg := zap.NewNop()
	dir := filepath.Join(t.TempDir(), "wal")
	w, err := etcdwal.Create(lg, dir, []byte("m"))
	if err != nil {
		t.Fatal(err)
	}
	saveEnts(t, w, 1, 30)
	if err := w.SaveSnapshot(pSnap(20)); err != nil {
		t.Fatal(err)
	}
	saveEnts(t, w, 31, 40)
	if n := len(walFiles(t, dir)); n < 6 {
		t.Fatalf("only %d WAL files", n)
	}
	return lg, dir, w
}

// readAt opens dir at the snapshot (i, purgeTerm) and reads it: the entries' indices, or err.
func readAt(lg *zap.Logger, dir string, i uint64) (*etcdwal.WAL, []uint64, error) {
	w, err := etcdwal.Open(lg, dir, &walpb.Snapshot{Index: newU64(i), Term: newU64(purgeTerm)})
	if err != nil {
		return nil, nil, err
	}
	_, _, ents, err := w.ReadAll()
	if err != nil {
		w.Close()
		return nil, nil, err
	}
	var idx []uint64
	for _, e := range ents {
		idx = append(idx, e.GetIndex())
	}
	return w, idx, nil
}

func wantRange(t *testing.T, got []uint64, lo, hi uint64) {
	t.Helper()
	if uint64(len(got)) != hi-lo+1 {
		t.Fatalf("read %d entries %v, want %d..%d", len(got), got, lo, hi)
	}
	for j, x := range got {
		if x != lo+uint64(j) {
			t.Fatalf("read %v, want %d..%d", got, lo, hi)
		}
	}
}

// After ReleaseLockTo(20), a round deletes the files before the one holding the snapshot record
// (unlocked), keeps that file and every later one (locked), and a graceful restart at the snapshot
// reads what it would have read without the round.
func TestPurgeRoundAfterReleaseLockTo(t *testing.T) {
	lg, dir, w := newPurgeWAL(t)
	before := walFiles(t, dir)
	if err := w.ReleaseLockTo(20); err != nil {
		t.Fatal(err)
	}
	purgeRound(lg, dir, 1)
	after := walFiles(t, dir)
	if len(after) >= len(before) {
		t.Fatalf("nothing deleted: %v", after)
	}
	t.Logf("files %d -> %d", len(before), len(after))
	// a suffix of the files remains, the first named at most 20 (it holds entry 20: ReleaseLockTo
	// keeps locked the files from the last one named below 20)
	if !equalStrings(after, before[len(before)-len(after):]) {
		t.Fatalf("not a suffix: before %v after %v", before, after)
	}
	if fileIndex(t, after[0]) > 20 {
		t.Fatalf("the file holding entry 21 was deleted: %v", after)
	}
	// a second round deletes nothing more (every remaining file is locked)
	purgeRound(lg, dir, 1)
	if again := walFiles(t, dir); !equalStrings(again, after) {
		t.Fatalf("second round deleted: %v -> %v", after, again)
	}
	saveEnts(t, w, 41, 45)
	if err := w.Close(); err != nil {
		t.Fatal(err)
	}
	w2, got, err := readAt(lg, dir, 20)
	if err != nil {
		t.Fatalf("restart after the purge: %v", err)
	}
	defer w2.Close()
	wantRange(t, got, 21, 45)
}

// After a restart's Open at the snapshot (which locks the files from the one holding it), a round
// deletes the earlier files; appending, closing and restarting again reads every entry.
func TestPurgeRoundAfterOpen(t *testing.T) {
	lg, dir, w := newPurgeWAL(t)
	if err := w.Close(); err != nil {
		t.Fatal(err)
	}
	before := walFiles(t, dir)
	w, got, err := readAt(lg, dir, 20)
	if err != nil {
		t.Fatal(err)
	}
	wantRange(t, got, 21, 40)
	purgeRound(lg, dir, 1)
	after := walFiles(t, dir)
	t.Logf("files %d -> %d", len(before), len(after))
	if len(after) >= len(before) {
		t.Fatalf("nothing deleted: %v", after)
	}
	if fileIndex(t, after[0]) > 20 {
		t.Fatalf("the file holding entry 21 was deleted: %v", after)
	}
	saveEnts(t, w, 41, 50)
	if err := w.Close(); err != nil {
		t.Fatal(err)
	}
	w2, got, err := readAt(lg, dir, 20)
	if err != nil {
		t.Fatalf("restart after the purge: %v", err)
	}
	defer w2.Close()
	wantRange(t, got, 21, 50)
}

// Right after Create, every file is locked (the WAL has released none): a round deletes nothing.
func TestPurgeRoundAllLocked(t *testing.T) {
	lg, dir, w := newPurgeWAL(t)
	defer w.Close()
	before := walFiles(t, dir)
	purgeRound(lg, dir, 1)
	if after := walFiles(t, dir); !equalStrings(after, before) {
		t.Fatalf("deleted locked files: %v -> %v", before, after)
	}
}

// The round goes oldest first and stops at the first file it cannot lock, even when a later file
// is unlocked (fileutil.purgeFile's loop).
func TestPurgeRoundStopsAtLocked(t *testing.T) {
	dir := t.TempDir()
	names := []string{"0000000000000000-0000000000000000.wal", "0000000000000001-0000000000000005.wal",
		"0000000000000002-0000000000000009.wal", "0000000000000003-000000000000000d.wal"}
	for _, n := range names {
		if err := os.WriteFile(filepath.Join(dir, n), []byte("x"), 0o600); err != nil {
			t.Fatal(err)
		}
	}
	l, err := fileutil.LockFile(filepath.Join(dir, names[1]), os.O_WRONLY, fileutil.PrivateFileMode)
	if err != nil {
		t.Fatal(err)
	}
	defer l.Close()
	purgeRound(zap.NewNop(), dir, 0)
	if after := walFiles(t, dir); !equalStrings(after, names[1:]) {
		t.Fatalf("got %v, want %v", after, names[1:])
	}
	// keep: the newest keep files are never deleted, locked or not
	l.Close()
	purgeRound(zap.NewNop(), dir, 2)
	if after := walFiles(t, dir); !equalStrings(after, names[2:]) {
		t.Fatalf("got %v, want %v", after, names[2:])
	}
}

// With no open handle nothing is locked: the round deletes every file but the newest, including
// those holding the entries after the snapshot record's index, and the restart at that snapshot
// fails. A purge spec without walOpenW and walPurgeW (whose unl bounds the deletion) would be false.
func TestPurgeRoundNoHandle(t *testing.T) {
	lg, dir, w := newPurgeWAL(t)
	if err := w.Close(); err != nil {
		t.Fatal(err)
	}
	purgeRound(lg, dir, 1)
	after := walFiles(t, dir)
	if len(after) != 1 {
		t.Fatalf("got %v, want one file", after)
	}
	if fileIndex(t, after[0]) <= 20 {
		t.Fatalf("the last file holds entry 21: %v (enlarge the test)", after)
	}
	if w2, got, err := readAt(lg, dir, 20); err == nil {
		w2.Close()
		t.Fatalf("restart at the purged snapshot read %v", got)
	}
}

func equalStrings(a, b []string) bool {
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

// copyFile copies src to dst (a file a power loss brings back).
func copyFile(t *testing.T, src, dst string) {
	t.Helper()
	b, err := os.ReadFile(src)
	if err != nil {
		t.Fatal(err)
	}
	if err := os.WriteFile(dst, b, 0o600); err != nil {
		t.Fatal(err)
	}
}

// purgeResurrect: a power loss after a round may undo any subset of its removes (no directory
// fsync; the unlinks can become durable out of order). After ReleaseLockTo(20) and a round, the
// deleted files numbered which (in the old listing) come back. A gap in the files (hole) makes
// ValidSnapshotEntries fail on the CRC chain (allowed: every read may fail;
// nonissues/etcd-wal-purge-unlink-gap.md), while Open+ReadAll at 20 still reads the full read
// (21..40, walReadCut I 0); a clean suffix keeps ValidSnapshotEntries working. The next round
// restores a suffix and a graceful restart reads 21..45. (From etcd-grove-81's axiom review of
// purgeRound, m4.)
func purgeResurrect(t *testing.T, which []int, hole bool) {
	lg, dir, w := newPurgeWAL(t)
	if err := w.ReleaseLockTo(20); err != nil {
		t.Fatal(err)
	}
	before := walFiles(t, dir)
	save := t.TempDir()
	for _, f := range before {
		copyFile(t, filepath.Join(dir, f), filepath.Join(save, f))
	}
	purgeRound(lg, dir, 1)
	if n := len(walFiles(t, dir)); n != len(before)-3 {
		t.Fatalf("the round deleted %d files, the test expects 3", len(before)-n)
	}
	if err := w.Close(); err != nil {
		t.Fatal(err)
	}
	for _, i := range which {
		copyFile(t, filepath.Join(save, before[i]), filepath.Join(dir, before[i]))
	}
	t.Logf("resurrected %v: %v", which, walFiles(t, dir))
	_, err := etcdwal.ValidSnapshotEntries(lg, dir)
	if hole && err == nil {
		t.Fatalf("ValidSnapshotEntries succeeded across a gap")
	}
	if !hole && err != nil {
		t.Fatalf("ValidSnapshotEntries on a suffix: %v", err)
	}
	w2, got, err := readAt(lg, dir, 20)
	if err != nil {
		t.Fatalf("restart read: %v", err)
	}
	wantRange(t, got, 21, 40)
	purgeRound(lg, dir, 0)
	saveEnts(t, w2, 41, 45)
	if err := w2.Close(); err != nil {
		t.Fatal(err)
	}
	if _, err := etcdwal.ValidSnapshotEntries(lg, dir); err != nil {
		t.Fatalf("ValidSnapshotEntries after the second round: %v", err)
	}
	w3, got, err := readAt(lg, dir, 20)
	if err != nil {
		t.Fatalf("graceful restart: %v", err)
	}
	defer w3.Close()
	wantRange(t, got, 21, 45)
}

func TestPurgeRoundResurrectNone(t *testing.T)   { purgeResurrect(t, nil, false) }
func TestPurgeRoundResurrectSuffix(t *testing.T) { purgeResurrect(t, []int{2}, false) }
func TestPurgeRoundResurrectHole0(t *testing.T)  { purgeResurrect(t, []int{0}, true) }
func TestPurgeRoundResurrectHole1(t *testing.T)  { purgeResurrect(t, []int{1}, true) }
func TestPurgeRoundResurrectHole02(t *testing.T) { purgeResurrect(t, []int{0, 2}, true) }

// Open at snapshot 0 (older than the one released to before) locks every file: nothing goes.
func TestPurgeRoundOpenOld(t *testing.T) {
	lg, dir, w := newPurgeWAL(t)
	if err := w.ReleaseLockTo(20); err != nil {
		t.Fatal(err)
	}
	if err := w.Close(); err != nil {
		t.Fatal(err)
	}
	w2, err := etcdwal.Open(lg, dir, &walpb.Snapshot{Index: newU64(0), Term: newU64(0)})
	if err != nil {
		t.Fatal(err)
	}
	defer w2.Close()
	if _, _, _, err := w2.ReadAll(); err != nil {
		t.Fatal(err)
	}
	n := len(walFiles(t, dir))
	purgeRound(lg, dir, 0)
	if m := len(walFiles(t, dir)); m != n {
		t.Fatalf("deleted %d files with every file locked", n-m)
	}
}
