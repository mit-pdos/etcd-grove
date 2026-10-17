package raft

import (
	"context"
	"testing"
	"time"

	pb "go.etcd.io/raft/v3/raftpb"
)

// TestPR88CallbackReentryHangs: DisableProposalForwardingCallback runs on the node's run
// goroutine, inside Step. A callback that consults the node (here n.Status(), a natural way to
// decide "am I still the leader?") blocks forever: the run loop that would answer is the one
// running the callback. Nothing in the Config documentation says the callback must not call into
// the node.
func TestPR88CallbackReentryHangs(t *testing.T) {
	s := newTestMemoryStorage(withPeers(1, 2))
	c := newTestConfig(1, 10, 1, s)
	var n Node
	c.DisableProposalForwardingCallback = func(m pb.Message) bool {
		return n.Status().RaftState != StateLeader // re-enters the node
	}
	rn, err := NewRawNode(c)
	if err != nil {
		t.Fatal(err)
	}
	nd := newNode(rn)
	n = &nd
	go nd.run()
	// no n.Stop(): a wedged loop would never answer it
	ctx, cancel := context.WithTimeout(context.Background(), 2*time.Second)
	defer cancel()
	// node 2 is leader at term 1: node 1 becomes its follower with a leader known
	if err := n.Step(ctx, pb.Message{Type: pb.MsgHeartbeat, From: 2, To: 1, Term: 1}); err != nil {
		t.Fatal(err)
	}
	err = n.Propose(ctx, []byte("x"))
	t.Logf("Propose returned %v", err)
	st := make(chan struct{})
	go func() { n.Status(); close(st) }()
	select {
	case <-st:
		t.Logf("Status answered: the node is live")
	case <-time.After(2 * time.Second):
		t.Fatalf("node wedged: the run loop is blocked in the callback (its n.Status() call waits for the loop itself); Propose: %v", err)
	}
}
