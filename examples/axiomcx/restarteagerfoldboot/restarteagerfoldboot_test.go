// Package restarteagerfoldboot is the end-to-end Go evidence for
// notes/axiom-review/bootstrap-restart-eagerfold.md: the WAL of restarteagerfold, made from a real
// member's files, restarted by etcd itself. A single-member etcd (embed.StartEtcd) starts and stops
// gracefully; the test then appends to its WAL a synced snapshot record at the saved commit + 10 (the
// shape no graceful etcd run writes: SaveSnap is always followed by a Save with commit at or above it,
// raft.go:269-276) and closes the WAL. Before the fix to walFiles (2026-11-28) these files met srvFiles
// (walRead of the history is sigma), while the restart contract's post asks for the eager fold to be sigma,
// which it is not. The restart (embed.StartEtcd again, through bootstrap) succeeds and the member is ready:
// bootstrap returns nil on files whose eager fold runs past the commit.
//
// Run: cd examples && go test ./axiomcx/restarteagerfoldboot/ -v
package restarteagerfoldboot

import (
	"path/filepath"
	"testing"
	"time"

	"go.etcd.io/etcd/server/v3/embed"
	"go.etcd.io/etcd/server/v3/storage/wal"
	"go.etcd.io/etcd/server/v3/storage/wal/walpb"
	"go.etcd.io/raft/v3/raftpb"
	"go.uber.org/zap"
)

func u(x uint64) *uint64 { return &x }

func start(t *testing.T, dir string) *embed.Etcd {
	cfg := embed.NewConfig()
	cfg.Dir = dir
	cfg.LogLevel = "error"
	e, err := embed.StartEtcd(cfg)
	if err != nil {
		t.Fatalf("StartEtcd: %v", err)
	}
	select {
	case <-e.Server.ReadyNotify():
	case <-time.After(20 * time.Second):
		t.Fatal("not ready")
	}
	return e
}

func TestRestartTrailingSnap(t *testing.T) {
	dir := t.TempDir()
	e := start(t, dir)
	id := uint64(e.Server.MemberID())
	e.Close()
	wd := filepath.Join(dir, "member", "wal")
	lg := zap.NewNop()
	snaps, err := wal.ValidSnapshotEntries(lg, wd)
	if err != nil {
		t.Fatal(err)
	}
	w, err := wal.Open(lg, wd, snaps[len(snaps)-1])
	if err != nil {
		t.Fatal(err)
	}
	_, st, es, err := w.ReadAll()
	if err != nil {
		t.Fatal(err)
	}
	c := st.GetCommit()
	last := es[len(es)-1]
	t.Logf("after graceful stop: commit %d last %d term %d", c, last.GetIndex(), st.GetTerm())
	if err := w.SaveSnapshot(&walpb.Snapshot{Index: u(c + 10), Term: u(st.GetTerm()), ConfState: &raftpb.ConfState{Voters: []uint64{id}}}); err != nil {
		t.Fatal(err)
	}
	w.Close()
	e2 := start(t, dir)
	t.Logf("restart ok: applied %d committed %d", e2.Server.AppliedIndex(), e2.Server.CommittedIndex())
	e2.Close()
}
