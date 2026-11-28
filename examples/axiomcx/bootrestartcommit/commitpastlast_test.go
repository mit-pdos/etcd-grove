package bootrestartcommit

// TestRestartCommitPastLast: why the restart's bootstrap contract takes the WAL's read facts as a premise
// (2026-11-27, the review of the interim axiom bootstrap.wp_proofRestart, R2;
// notes/axiom-review/bootstrap-restart-walreadfacts.md). A member is started and stopped gracefully, then its
// WAL is given one more record through etcd's own wal package: a hard state whose commit is past the last
// entry. wal.ReadAll returns it unchecked, bootstrap's restart branch succeeds, and raft's RestartNode
// panics in loadState ("commit ... is out of range"). So the records a restart reads need not satisfy
// I3 (commit <= last); only a graceful stop's do. (The reviewer's test ran through embed.StartEtcd at the
// fork; this one starts a member as examples/etcd/restart1 does, at the pinned etcd.) Its own package: it
// leaves the panicked member's resources behind.

import (
	"fmt"
	"testing"
	"time"

	"go.uber.org/zap"

	"go.etcd.io/etcd/client/pkg/v3/types"
	"go.etcd.io/etcd/server/v3/etcdserver"

	"go.etcd.io/etcd/server/v3/storage/wal"
	"go.etcd.io/raft/v3/raftpb"

	"github.com/mit-pdos/etcd-grove/examples/lib/etcdstart"
	"github.com/mit-pdos/etcd-grove/examples/lib/walarea"
)

func TestRestartCommitPastLast(t *testing.T) {
	t.Chdir(t.TempDir())
	walarea.Reset(t, name)
	lg := zap.NewNop()
	s, err := startMember(lg)
	if err != nil {
		t.Fatal(err)
	}
	stop(s)

	walDir := etcdstart.WALBase + "/" + name + ".etcd" + "/wal"
	snaps, err := wal.ValidSnapshotEntries(lg, walDir)
	if err != nil {
		t.Fatal(err)
	}
	last := snaps[len(snaps)-1]
	w, err := wal.Open(lg, walDir, last)
	if err != nil {
		t.Fatal(err)
	}
	_, st, ents, err := w.ReadAll()
	if err != nil {
		t.Fatal(err)
	}
	lastIdx := last.GetIndex()
	if len(ents) > 0 {
		lastIdx = ents[len(ents)-1].GetIndex()
	}
	t.Logf("before: commit=%d last=%d", st.GetCommit(), lastIdx)
	hs := &raftpb.HardState{Term: new(st.GetTerm()), Vote: new(st.GetVote()), Commit: new(lastIdx + 5)}
	if err := w.Save(hs, nil); err != nil {
		t.Fatal(err)
	}
	w.Close()

	p := func() (p any) {
		defer func() { p = recover() }()
		if _, err := startMember(lg); err != nil {
			t.Logf("restart returned an error: %v", err)
		}
		return nil
	}()
	if p == nil {
		t.Fatal("the restart did not panic")
	}
	t.Logf("the restart panicked: %v", fmt.Sprint(p))
}

const (
	name       = "bootrestartcommit"
	peerAddr   = "127.0.0.1:23831"
	clientAddr = "127.0.0.1:23832"
)

// startMember builds and starts the one member (restart1's startMember, at this test's name).
func startMember(lg *zap.Logger) (*etcdserver.EtcdServer, error) {
	peer := types.URLs{{Scheme: "http", Host: peerAddr}}
	s, err := etcdstart.BuildServer(name, peer, clientAddr, types.URLsMap{name: peer}, name, 1, 1, lg)
	if err != nil {
		return nil, err
	}
	s.Start()
	return s, nil
}

// stop waits until the member applied its bootstrap entry, then stops it (restart1's stop).
func stop(s *etcdserver.EtcdServer) {
	for s.AppliedIndex() < 1 {
		time.Sleep(time.Millisecond)
	}
	s.HardStop()
}
