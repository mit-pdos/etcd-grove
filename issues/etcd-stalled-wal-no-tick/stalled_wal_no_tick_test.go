// Reproduction of issues/etcd-stalled-wal-no-tick.md (etcd-io/etcd#13527).
//
// Drop into package etcdserver of go.etcd.io/etcd/server/v3 (directory server/etcdserver of
// upamanyus/etcd at 107edf7e4, the pin of etc/goose.py; also etcd-io/etcd main at ea8b59433),
// next to server_test.go, whose helpers it uses (newNopReadyNode, newNopTransporter), and run
//
//	cd server && go test ./etcdserver -run TestStalledWALStopsTicks -count=1
//
// It passes at the pin, showing the bug: raftNode.start's loop calls the WAL's Save inline, in the
// same select loop that delivers ticker ticks to raft (r.tick() → Node.Tick). While Save blocks (a
// stalled disk), no tick reaches raft, so a leader's CheckQuorum never fires and it never steps
// down, though it is partitioned from every follower.
package etcdserver

import (
	"sync"
	"testing"
	"time"

	"go.uber.org/zap/zaptest"

	"go.etcd.io/etcd/server/v3/mock/mockstorage"
	"go.etcd.io/raft/v3"
	"go.etcd.io/raft/v3/raftpb"
)

// stalledStorage is a WAL whose Save blocks until release is closed.
type stalledStorage struct {
	*mockstorage.StorageRecorder
	entered chan struct{}
	release chan struct{}
}

func (s *stalledStorage) Save(st *raftpb.HardState, ents []*raftpb.Entry) error {
	close(s.entered)
	<-s.release
	return s.StorageRecorder.Save(st, ents)
}

func countTicks(n *readyNode) int {
	c := 0
	for _, a := range n.Action() {
		if a.Name == "Tick" {
			c++
		}
	}
	return c
}

func TestStalledWALStopsTicks(t *testing.T) {
	n := newNopReadyNode()
	st := &stalledStorage{mockstorage.NewStorageRecorder(""), make(chan struct{}), make(chan struct{})}
	r := newRaftNode(raftNodeConfig{
		lg:          zaptest.NewLogger(t),
		Node:        n,
		storage:     st,
		raftStorage: raft.NewMemoryStorage(),
		transport:   newNopTransporter(),
		heartbeat:   5 * time.Millisecond,
	})
	srv := &EtcdServer{lgMu: new(sync.RWMutex), lg: zaptest.NewLogger(t), r: *r}
	srv.r.start(&raftReadyHandler{
		getLead:          func() uint64 { return 1 },
		updateLead:       func(uint64) {},
		updateLeadership: func(bool) {},
	})
	var once sync.Once
	unblock := func() { once.Do(func() { close(st.release) }) }
	defer func() { unblock(); srv.r.stop() }()

	// Ticks are delivered while the loop is idle.
	time.Sleep(100 * time.Millisecond)
	if c := countTicks(n); c == 0 {
		t.Fatalf("no tick delivered while idle")
	}

	// A leader's Ready with entries to persist: the loop sends to applyc, then calls Save, which stalls.
	idx, term := uint64(1), uint64(1)
	n.readyc <- raft.Ready{
		SoftState: &raft.SoftState{Lead: 1, RaftState: raft.StateLeader},
		Entries:   []*raftpb.Entry{{Index: &idx, Term: &term}},
	}
	<-srv.r.applyc
	<-st.entered

	before := countTicks(n)
	time.Sleep(200 * time.Millisecond) // 40 heartbeat intervals
	after := countTicks(n)
	if after != before {
		t.Fatalf("ticks delivered while the WAL stalls: %d -> %d (bug not reproduced)", before, after)
	}
	t.Logf("no tick in 200ms (40 heartbeat intervals) while Save stalls; %d ticks before", before)
	unblock()
}
