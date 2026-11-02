// Test of nonissues/etcd-leader-advance-before-applyconfchange.md: copy into server/etcdserver/ and
// run `go test ./etcdserver -run '^TestLeaderConfigChangeBlocksApply$'` from server/. It is
// TestConfigChangeBlocksApply (raft_test.go) with the Ready of a leader instead of a follower, and
// uses the package's test helpers newNopReadyNode and newNopTransporter.
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

// TestLeaderConfigChangeBlocksApply ensures that, on a leader as on a follower, the raft loop does
// not advance raft past a Ready whose committed entries contain a config change before the apply
// loop has applied them.
func TestLeaderConfigChangeBlocksApply(t *testing.T) {
	n := newNopReadyNode()

	r := newRaftNode(raftNodeConfig{
		lg:          zaptest.NewLogger(t),
		Node:        n,
		storage:     mockstorage.NewStorageRecorder(""),
		raftStorage: raft.NewMemoryStorage(),
		transport:   newNopTransporter(),
	})
	srv := &EtcdServer{lgMu: new(sync.RWMutex), lg: zaptest.NewLogger(t), r: *r}

	srv.r.start(&raftReadyHandler{
		getLead:          func() uint64 { return 0 },
		updateLead:       func(uint64) {},
		updateLeadership: func(bool) {},
	})
	defer srv.r.stop()

	n.readyc <- raft.Ready{
		SoftState:        &raft.SoftState{RaftState: raft.StateLeader},
		CommittedEntries: []*raftpb.Entry{{Type: raftpb.EntryConfChange.Enum()}},
	}
	ap := <-srv.r.applyc

	continueC := make(chan struct{})
	go func() {
		n.readyc <- raft.Ready{}
		<-srv.r.applyc
		close(continueC)
	}()

	select {
	case <-continueC:
		t.Fatalf("unexpected execution: raft routine should block waiting for toApply")
	case <-time.After(time.Second):
	}

	// finish toApply, unblock raft routine
	<-ap.notifyc

	<-ap.raftAdvancedC
	t.Log("received raft advance notification")

	select {
	case <-continueC:
	case <-time.After(time.Second):
		t.Fatalf("unexpected blocking on execution")
	}
}
