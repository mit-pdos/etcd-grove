package wallink

import (
	"bytes"
	"errors"
	"fmt"
	"go/ast"
	"go/parser"
	"go/token"
	"math/rand"
	"os"
	"path/filepath"
	"sync"
	"testing"

	"go.uber.org/zap"
	"google.golang.org/protobuf/proto"

	"go.etcd.io/etcd/server/v3/etcdserver/api/snap"
	serverstorage "go.etcd.io/etcd/server/v3/storage"
	"go.etcd.io/etcd/server/v3/storage/wal"
	"go.etcd.io/etcd/server/v3/storage/wal/walpb"
	"go.etcd.io/raft/v3/raftpb"
)

// ---------------------------------------------------------------- the server-side model (layer 2)

// ent is an entry of the model (EntryM, without the type).
type ent struct {
	term, index uint64
	data        []byte
}

// recs is StorContents: the hard state, the base (the snapshot record's index and term), the
// entries above the base (WalRecsCore.lean, WalRecs.lean).
type recs struct {
	term, vote, commit uint64
	bTerm, bIndex      uint64
	ents               []ent
}

// save is walSave: the hard state replaced unless empty (phsNext), the entries truncate-appended
// (appendEnts: ents.take(e0.index - b - 1) ++ es).
func (r recs) save(term, vote, commit uint64, es []ent) recs {
	if !(term == 0 && vote == 0 && commit == 0) {
		r.term, r.vote, r.commit = term, vote, commit
	}
	if len(es) > 0 {
		k := int(es[0].index - r.bIndex - 1)
		n := append([]ent{}, r.ents[:k]...)
		r.ents = append(n, es...)
	}
	return r
}

// saveSnap is walSaveSnap: below the base nothing; else the base moves to m, the entries above it
// kept when m is within the commit, dropped otherwise.
func (r recs) saveSnap(term, index uint64) recs {
	if index < r.bIndex {
		return r
	}
	if index <= r.commit {
		d := int(index - r.bIndex)
		if d > len(r.ents) {
			d = len(r.ents)
		}
		r.ents = append([]ent{}, r.ents[d:]...)
	} else {
		r.ents = nil
	}
	r.bTerm, r.bIndex = term, index
	return r
}

func (r recs) last() uint64 { return r.bIndex + uint64(len(r.ents)) }

// ---------------------------------------------------------------- helpers

func u64(x uint64) *uint64 { return &x }

func cs() *raftpb.ConfState { return &raftpb.ConfState{Voters: []uint64{1}} }

func rEnts(es []ent) []*raftpb.Entry {
	out := make([]*raftpb.Entry, len(es))
	for i, e := range es {
		out[i] = &raftpb.Entry{Term: u64(e.term), Index: u64(e.index), Type: raftpb.EntryNormal.Enum(),
			Data: e.data}
	}
	return out
}

// readBack is a restart's read as bootstrap does it (recoverSnapshot's ValidSnapshotEntries and
// newestSnapshotEntry, then openWALFromSnapshot's Open and ReadAll).
func readBack(t *testing.T, lg *zap.Logger, dir string) recs {
	t.Helper()
	r, err := tryReadBack(lg, dir)
	if err != nil {
		t.Fatal(err)
	}
	return r
}

func tryReadBack(lg *zap.Logger, dir string) (recs, error) {
	snaps, err := wal.ValidSnapshotEntries(lg, dir)
	if err != nil {
		return recs{}, fmt.Errorf("ValidSnapshotEntries: %w", err)
	}
	idx := 0
	for i, s := range snaps {
		if s.GetIndex() >= snaps[idx].GetIndex() {
			idx = i
		}
	}
	ws := &walpb.Snapshot{Index: u64(snaps[idx].GetIndex()), Term: u64(snaps[idx].GetTerm())}
	w, err := wal.Open(lg, dir, ws)
	if err != nil {
		return recs{}, fmt.Errorf("Open: %w", err)
	}
	defer w.Close()
	_, st, ents, err := w.ReadAll()
	if err != nil {
		return recs{}, fmt.Errorf("ReadAll: %w", err)
	}
	r := recs{term: st.GetTerm(), vote: st.GetVote(), commit: st.GetCommit(),
		bTerm: ws.GetTerm(), bIndex: ws.GetIndex()}
	for _, e := range ents {
		r.ents = append(r.ents, ent{e.GetTerm(), e.GetIndex(), e.GetData()})
	}
	return r, nil
}

func eq(a, b recs) bool {
	if a.term != b.term || a.vote != b.vote || a.commit != b.commit || a.bIndex != b.bIndex ||
		a.bTerm != b.bTerm || len(a.ents) != len(b.ents) {
		return false
	}
	for i := range a.ents {
		x, y := a.ents[i], b.ents[i]
		if x.term != y.term || x.index != y.index || !bytes.Equal(x.data, y.data) {
			return false
		}
	}
	return true
}

func tmp(t *testing.T) string {
	t.Helper()
	d, err := os.MkdirTemp(os.Getenv("TMPDIR"), "wallink-")
	if err != nil {
		t.Fatal(err)
	}
	t.Cleanup(func() { os.RemoveAll(d) })
	return d
}

// ---------------------------------------------------------------- C1: the eager model reads back

// TestEagerModelReadsBack (Scope §3.1, the read bridge): for random server-shaped histories (each
// Save's entries consecutive, above the base, the first at most one past the last: WalSaveOk; the
// commit within the last index; own snapshots within the commit, possibly below the base; received
// snapshots above the commit, followed by the raft loop's Save of a hard state committing them),
// written through the server's storage wrapper and closed gracefully, a restart's read equals the
// eager model (walSave/walSaveSnap folded) whenever its base is within its commit. Also counts the
// runs with the base above the commit (a received snapshot not yet followed by its Save), where the
// read differs: walRecs promises the read only under `σ.b ≤ σ.commit`.
func TestEagerModelReadsBack(t *testing.T) {
	lg := zap.NewNop()
	rng := rand.New(rand.NewSource(1))
	agree, guarded, differ := 0, 0, 0
	for run := 0; run < 200; run++ {
		root := tmp(t)
		dir := filepath.Join(root, "wal")
		w, err := wal.Create(lg, dir, []byte("md"))
		if err != nil {
			t.Fatal(err)
		}
		st := serverstorage.NewStorage(lg, w, snap.New(lg, filepath.Join(root, "snap")))
		m := recs{}
		term := uint64(1)
		steps := 1 + rng.Intn(25)
		for s := 0; s < steps; s++ {
			switch k := rng.Intn(10); {
			case k < 6: // Save: a batch at most one past the last, above the base
				lo := m.bIndex + 1
				if m.last() >= lo {
					lo = m.bIndex + 1 + uint64(rng.Intn(int(m.last()-m.bIndex)+1))
				}
				if rng.Intn(4) == 0 {
					term++
				}
				n := rng.Intn(4)
				var es []ent
				for i := 0; i < n; i++ {
					es = append(es, ent{term, lo + uint64(i), []byte(fmt.Sprintf("r%ds%di%d", run, s, i))})
				}
				nm := m.save(0, 0, 0, es)
				commit := m.commit
				if nm.last() > commit && rng.Intn(2) == 0 {
					commit += uint64(rng.Intn(int(nm.last()-commit) + 1))
				}
				if commit > nm.last() {
					commit = nm.last()
				}
				if commit < m.commit { // a truncation below the commit: raft never does it
					continue
				}
				if err := st.Save(&raftpb.HardState{Term: u64(term), Vote: u64(1), Commit: u64(commit)},
					rEnts(es)); err != nil {
					t.Fatal(err)
				}
				m = m.save(term, 1, commit, es)
			case k < 8: // own snapshot within the commit (possibly below the base)
				if m.commit == 0 {
					continue
				}
				i := 1 + uint64(rng.Intn(int(m.commit)))
				tm := term
				if i > m.bIndex && i <= m.last() {
					tm = m.ents[i-m.bIndex-1].term
				} else if i == m.bIndex {
					tm = m.bTerm
				}
				if err := st.SaveSnap(&raftpb.Snapshot{Metadata: &raftpb.SnapshotMetadata{
					Index: u64(i), Term: u64(tm), ConfState: cs()}}); err != nil {
					t.Fatal(err)
				}
				m = m.saveSnap(tm, i)
			default: // received snapshot above the commit, usually followed by its Save
				i := m.last() + 1 + uint64(rng.Intn(3))
				term++
				if err := st.SaveSnap(&raftpb.Snapshot{Metadata: &raftpb.SnapshotMetadata{
					Index: u64(i), Term: u64(term), ConfState: cs()}}); err != nil {
					t.Fatal(err)
				}
				m = m.saveSnap(term, i)
				if rng.Intn(5) != 0 {
					if err := st.Save(&raftpb.HardState{Term: u64(term), Vote: u64(1), Commit: u64(i)},
						nil); err != nil {
						t.Fatal(err)
					}
					m = m.save(term, 1, i, nil)
				}
			}
		}
		if err := st.Close(); err != nil {
			t.Fatal(err)
		}
		got, rerr := tryReadBack(lg, dir)
		if m.bIndex <= m.commit {
			if rerr != nil {
				t.Fatalf("run %d: base within commit, read failed: %v (model %+v)", run, rerr, m)
			}
			if !eq(got, m) {
				t.Fatalf("run %d: base within commit, read %+v, model %+v", run, got, m)
			}
			agree++
		} else {
			guarded++
			if rerr != nil || !eq(got, m) {
				differ++
			}
		}
	}
	t.Logf("agree (b <= commit): %d; b > commit: %d (read fails or differs from the eager model in %d)",
		agree, guarded, differ)
	if differ == 0 {
		t.Fatalf("expected the guard b <= commit to matter in some run")
	}
}

// ---------------------------------------------------------------- C2: concurrent clients

// TestStorageConcurrentClients (Scope §3.2, the shared handle): the server's storage takes only its
// read lock in Save, SaveSnap, Release and Sync (storage.go), so the raft loop's Save and the apply
// thread's SaveSnap and Release run at once; the WAL's own mutex (w.mu, taken first by each of
// Save, SaveSnapshot, ReleaseLockTo, Sync and Close) is what serializes them. Run with -race: no
// race, and every saved entry reads back.
func TestStorageConcurrentClients(t *testing.T) {
	lg := zap.NewNop()
	root := tmp(t)
	dir := filepath.Join(root, "wal")
	w, err := wal.Create(lg, dir, []byte("md"))
	if err != nil {
		t.Fatal(err)
	}
	st := serverstorage.NewStorage(lg, w, snap.New(lg, filepath.Join(root, "snap")))
	if err := os.MkdirAll(filepath.Join(root, "snap"), 0o700); err != nil {
		t.Fatal(err)
	}
	const n = 2000
	var wg sync.WaitGroup
	commitc := make(chan uint64, n)
	wg.Add(2)
	go func() { // the raft loop
		defer wg.Done()
		defer close(commitc)
		for i := uint64(1); i <= n; i++ {
			if err := st.Save(&raftpb.HardState{Term: u64(1), Vote: u64(1), Commit: u64(i)},
				rEnts([]ent{{1, i, bytes.Repeat([]byte{byte(i)}, 4096)}})); err != nil {
				t.Error(err)
				return
			}
			commitc <- i
		}
	}()
	go func() { // the apply thread's snapshots
		defer wg.Done()
		for i := range commitc {
			if i%97 != 0 {
				continue
			}
			s := &raftpb.Snapshot{Metadata: &raftpb.SnapshotMetadata{Index: u64(i), Term: u64(1),
				ConfState: cs()}}
			if err := st.SaveSnap(s); err != nil {
				t.Error(err)
				return
			}
			if err := st.Release(s); err != nil {
				t.Error(err)
				return
			}
		}
	}()
	wg.Wait()
	if err := st.Close(); err != nil {
		t.Fatal(err)
	}
	got := readBack(t, lg, dir)
	if got.commit != n || got.last() != n {
		t.Fatalf("read back commit %d last %d, want %d", got.commit, got.last(), n)
	}
	t.Logf("base %d, %d entries above it", got.bIndex, len(got.ents))
}

// ---------------------------------------------------------------- C3: SaveSnap's conf state

// TestSaveSnapNeedsConfState (Scope §3.3, SaveSnapshot's premise `md.Index = 0 ∨ cs`): the
// storage's SaveSnap builds the WAL's record with `GetConfState()`; a snapshot of a positive index
// whose metadata has no conf state is refused by `ValidateSnapshotForWrite` (an error, on which the
// apply thread panics, server.go:2158-2159), and nothing is written. A conf state present but empty
// survives the wire (proto2 presence), so a received snapshot keeps it.
func TestSaveSnapNeedsConfState(t *testing.T) {
	lg := zap.NewNop()
	root := tmp(t)
	w, err := wal.Create(lg, filepath.Join(root, "wal"), []byte("md"))
	if err != nil {
		t.Fatal(err)
	}
	st := serverstorage.NewStorage(lg, w, snap.New(lg, filepath.Join(root, "snap")))
	defer st.Close()
	if err := st.Save(&raftpb.HardState{Term: u64(1), Commit: u64(1)}, rEnts([]ent{{1, 1, nil}})); err != nil {
		t.Fatal(err)
	}
	err = st.SaveSnap(&raftpb.Snapshot{Metadata: &raftpb.SnapshotMetadata{Index: u64(1), Term: u64(1)}})
	if err == nil {
		t.Fatalf("SaveSnap of index 1 without a conf state succeeded")
	}
	t.Logf("SaveSnap without conf state: %v", err)
	if err := st.SaveSnap(&raftpb.Snapshot{Metadata: &raftpb.SnapshotMetadata{Index: u64(0), Term: u64(0)}}); err != nil {
		t.Fatalf("SaveSnap of index 0 without a conf state: %v", err)
	}
	in := &raftpb.Snapshot{Metadata: &raftpb.SnapshotMetadata{Index: u64(5), Term: u64(2),
		ConfState: &raftpb.ConfState{}}}
	b, err := proto.Marshal(in)
	if err != nil {
		t.Fatal(err)
	}
	var out raftpb.Snapshot
	if err := proto.Unmarshal(b, &out); err != nil {
		t.Fatal(err)
	}
	if out.GetMetadata().GetConfState() == nil {
		t.Fatalf("an empty conf state was lost on the wire")
	}
}

// ---------------------------------------------------------------- C4: no write after Close

// TestSaveAfterClosePanics (Scope §3.2, why `walOpen w 1` closes: no write follows a close): after
// the storage's Close, a Save that must cut or write panics or fails; layer 1's Close consumes the
// handle, layer 2's takes the whole open token.
func TestSaveAfterClosePanics(t *testing.T) {
	lg := zap.NewNop()
	root := tmp(t)
	w, err := wal.Create(lg, filepath.Join(root, "wal"), []byte("md"))
	if err != nil {
		t.Fatal(err)
	}
	st := serverstorage.NewStorage(lg, w, snap.New(lg, filepath.Join(root, "snap")))
	if err := st.Close(); err != nil {
		t.Fatal(err)
	}
	var res string
	func() {
		defer func() {
			if r := recover(); r != nil {
				res = fmt.Sprintf("panic: %v", r)
			}
		}()
		err := st.Save(&raftpb.HardState{Term: u64(1), Commit: u64(1)}, rEnts([]ent{{1, 1, nil}}))
		res = fmt.Sprintf("returned %v", err)
	}()
	t.Logf("Save after Close: %s", res)
	if res == "returned <nil>" {
		t.Fatalf("Save after Close succeeded")
	}
}

// ---------------------------------------------------------------- C5: several WALs in a process

// TestCreateWhileAnotherWALCuts (Scope §4.3, one WAL per process in layer 1): etcd allows a second
// member's wal.Create (a directory rename, dir.tmp to dir) while the first member's WAL appends and
// cuts (its own renames and the file pipeline's creates, path calls in another directory) in the
// same process, as the examples' StartMembers does (member j's bootstrap runs after member j-1's
// Start). Linux resolves the disjoint paths independently; every WAL reads back. Layer 1's model
// (fsExt: a directory rename is stuck while any other path call is in flight; the lock token and
// `osCallPerm 1` per generation) excludes this run.
func TestCreateWhileAnotherWALCuts(t *testing.T) {
	lg := zap.NewNop()
	root := tmp(t)
	old := wal.SegmentSizeBytes
	wal.SegmentSizeBytes = 64 * 1024 // cut often
	defer func() { wal.SegmentSizeBytes = old }()
	w0, err := wal.Create(lg, filepath.Join(root, "m0", "member", "wal"), []byte("md0"))
	if err != nil {
		t.Fatal(err)
	}
	const n = 600
	done := make(chan error, 1)
	go func() {
		for i := uint64(1); i <= n; i++ {
			if err := w0.Save(&raftpb.HardState{Term: u64(1), Commit: u64(i)},
				rEnts([]ent{{1, i, bytes.Repeat([]byte{1}, 1024)}})); err != nil {
				done <- err
				return
			}
		}
		done <- nil
	}()
	var ws []*wal.WAL
	for j := 1; j <= 20; j++ {
		w, err := wal.Create(lg, filepath.Join(root, fmt.Sprintf("m%d", j), "member", "wal"), []byte("md"))
		if err != nil {
			t.Fatalf("Create %d: %v", j, err)
		}
		ws = append(ws, w)
	}
	if err := <-done; err != nil {
		t.Fatal(err)
	}
	for _, w := range append(ws, w0) {
		if err := w.Close(); err != nil {
			t.Fatal(err)
		}
	}
	got := readBack(t, lg, filepath.Join(root, "m0", "member", "wal"))
	if got.last() != n {
		t.Fatalf("member 0 read back to %d, want %d", got.last(), n)
	}
	names, _ := filepath.Glob(filepath.Join(root, "m0", "member", "wal", "*.wal"))
	t.Logf("member 0: %d segments; 20 WALs created meanwhile", len(names))
	if len(names) < 2 {
		t.Fatalf("no cut happened")
	}
}

// ---------------------------------------------------------------- C6: Release needs no record

// TestReleaseLockToWithoutRecord (Scope §3.4, Release's witness): Go's ReleaseLockTo(a) needs no
// snapshot record at a (it only compares the lock files' first indices with a), while layer 1's
// spec takes a synced snapshot record of index a; the server always releases at a snapshot it saved
// before (server.go:2158/2162; raft.go:257 before applySnapshot's server.go:1122), so the stronger
// premise is met, through a witness the SaveSnap law must give.
func TestReleaseLockToWithoutRecord(t *testing.T) {
	lg := zap.NewNop()
	root := tmp(t)
	old := wal.SegmentSizeBytes
	wal.SegmentSizeBytes = 16 * 1024
	defer func() { wal.SegmentSizeBytes = old }()
	w, err := wal.Create(lg, filepath.Join(root, "wal"), []byte("md"))
	if err != nil {
		t.Fatal(err)
	}
	defer w.Close()
	for i := uint64(1); i <= 200; i++ {
		if err := w.Save(&raftpb.HardState{Term: u64(1), Commit: u64(i)},
			rEnts([]ent{{1, i, bytes.Repeat([]byte{2}, 512)}})); err != nil {
			t.Fatal(err)
		}
	}
	if err := w.ReleaseLockTo(150); err != nil && !errors.Is(err, os.ErrNotExist) {
		t.Fatalf("ReleaseLockTo without a record: %v", err)
	}
}

// ---------------------------------------------------------------- C7: the examples purge no WAL file

// TestExamplesPurgeNoWAL (Scope §1, item 8, and §4.4): the server's purgeFile purges WAL files only
// when `Cfg.MaxWALFiles > 0` (server.go:612-614); no example's configuration sets the field
// (examples/lib/etcdstart builds every member's `config.ServerConfig` and leaves it zero), so in
// every closed theorem's program purgeFile only waits for `stopping`. Checked on the syntax trees:
// no Go file of the examples' start code or of an example assigns the field.
func TestExamplesPurgeNoWAL(t *testing.T) {
	roots := []string{"../lib", "../etcd", "../k8s"}
	n := 0
	for _, r := range roots {
		err := filepath.Walk(r, func(p string, info os.FileInfo, err error) error {
			if err != nil || info.IsDir() || filepath.Ext(p) != ".go" {
				return err
			}
			fset := token.NewFileSet()
			f, perr := parser.ParseFile(fset, p, nil, 0)
			if perr != nil {
				return nil
			}
			n++
			ast.Inspect(f, func(x ast.Node) bool {
				switch v := x.(type) {
				case *ast.KeyValueExpr:
					if id, ok := v.Key.(*ast.Ident); ok && id.Name == "MaxWALFiles" {
						t.Errorf("%s: MaxWALFiles set", fset.Position(v.Pos()))
					}
				case *ast.SelectorExpr:
					if v.Sel.Name == "MaxWALFiles" {
						t.Errorf("%s: MaxWALFiles used", fset.Position(v.Pos()))
					}
				}
				return true
			})
			return nil
		})
		if err != nil {
			t.Fatal(err)
		}
	}
	t.Logf("%d Go files checked", n)
}
