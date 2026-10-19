package kv

import (
	"sync/atomic"
	"testing"
	"time"

	"github.com/anishathalye/porcupine"
	"go.etcd.io/raft/v3"
	pb "go.etcd.io/raft/v3/raftpb"

	"github.com/mit-pdos/etcd-grove/examples/lintest"
)

// The randomized linearizability test on two voters and a witness.
func TestWitnessCheck(t *testing.T) {
	if r := Check(StartClusterWitness([]uint64{1, 2}, 3), lintest.CounterClock(), 4, 30); r != porcupine.Ok {
		t.Fatalf("porcupine: %v", r)
	}
}

// TestWitnessNodeDown runs voters 1 and 2 and the witness 3, with the transport dropping
// every message to or from replica 2 while it is down: the leader then commits with the
// witness, and replica 2, back, catches up.
func TestWitnessNodeDown(t *testing.T) {
	voters := []uint64{1, 2}
	members := []uint64{1, 2, 3}
	var down atomic.Uint64
	peers := make(map[uint64]raft.Node)
	storages := make(map[uint64]*Storage)
	for _, id := range voters {
		st := &Storage{MemoryStorage: raft.NewMemoryStorage(), voters: members, witness: 3}
		peers[id] = raft.RestartNode(&raft.Config{
			ID: id, ElectionTick: 10, HeartbeatTick: 1, Storage: st,
			MaxSizePerMsg: 1 << 20, MaxInflightMsgs: 256, Logger: quietLogger{},
			CheckQuorum: true, StepDownOnRemoval: true,
		})
		storages[id] = st
	}
	tr := &transfers{left: timeouts}
	send := func(ms []*pb.Message) {
		var up []*pb.Message
		for _, m := range ms {
			if d := down.Load(); d != 0 && (m.GetTo() == d || m.GetFrom() == d) {
				continue
			}
			up = append(up, m)
		}
		deliver(peers, tr, up)
	}
	stop := make(chan struct{})
	defer func() {
		close(stop)
		for _, nd := range peers {
			nd.Stop()
		}
	}()
	ws := NewWitnessStore()
	regs := make(map[uint64]*KV)
	for _, id := range voters {
		w := raft.NewWitness(raft.WitnessConfig{ID: 3, Storage: ws, CheckQuorum: true})
		regs[id] = newKV(id, peers[id], storages[id], send, w)
		// a node that is down does not tick either (it would campaign, through the witness)
		go func(id uint64, nd raft.Node) {
			tk := time.NewTicker(5 * time.Millisecond)
			defer tk.Stop()
			for {
				select {
				case <-tk.C:
					if down.Load() != id {
						nd.Tick()
					}
				case <-stop:
					return
				}
			}
		}(id, peers[id])
	}
	regs[1].Put("k", "a")
	// replica 1 the leader, so that it is the one left with the witness
	deadline := time.Now().Add(10 * time.Second)
	for peers[1].Status().RaftState != raft.StateLeader {
		if time.Now().After(deadline) {
			t.Fatal("replica 1 did not become the leader")
		}
		regs[1].TransferLeadership(1)
		regs[2].TransferLeadership(1)
		time.Sleep(20 * time.Millisecond)
	}
	down.Store(2)
	done := make(chan struct{})
	go func() {
		regs[1].Put("k", "b")
		close(done)
	}()
	select {
	case <-done:
	case <-time.After(20 * time.Second):
		t.Fatal("a Put with replica 2 down did not commit")
	}
	if v := regs[1].Get("k"); v != "b" {
		t.Fatalf("replica 1: Get = %q, want b", v)
	}
	ws.mu.Lock()
	lt := ws.state.GetLastLogTerm()
	ws.mu.Unlock()
	if lt == 0 {
		t.Fatal("the witness was not written: b did not commit with it")
	}
	down.Store(0)
	if v := regs[2].Get("k"); v != "b" {
		t.Fatalf("replica 2, back: Get = %q, want b", v)
	}
}
