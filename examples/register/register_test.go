package register

import (
	"context"
	"testing"
	"time"

	"go.etcd.io/raft/v3"
	pb "go.etcd.io/raft/v3/raftpb"
)

// cluster starts n replicas connected in process, with a ticker each.
func cluster(t *testing.T, n int) ([]*Register, func()) {
	var voters []uint64
	for i := 1; i <= n; i++ {
		voters = append(voters, uint64(i))
	}
	nodes := make([]raft.Node, n)
	regs := make([]*Register, n)
	send := func(ms []pb.Message) {
		for _, m := range ms {
			m := m
			go nodes[m.To-1].Step(context.Background(), m)
		}
	}
	stop := make(chan struct{})
	for i := 0; i < n; i++ {
		st := NewStorage(voters)
		c := &raft.Config{
			ID:              uint64(i + 1),
			ElectionTick:    10,
			HeartbeatTick:   1,
			Storage:         st,
			MaxSizePerMsg:   1 << 20,
			MaxInflightMsgs: 256,
		}
		nodes[i] = raft.RestartNode(c)
		regs[i] = New(uint64(i+1), nodes[i], st, send)
		go func(nd raft.Node) {
			tk := time.NewTicker(5 * time.Millisecond)
			defer tk.Stop()
			for {
				select {
				case <-tk.C:
					nd.Tick()
				case <-stop:
					return
				}
			}
		}(nodes[i])
	}
	return regs, func() {
		close(stop)
		for _, nd := range nodes {
			nd.Stop()
		}
	}
}

func TestPutGet(t *testing.T) {
	regs, stop := cluster(t, 3)
	defer stop()
	if v := regs[0].Get(); v != "" {
		t.Fatalf("initial Get = %q, want empty", v)
	}
	regs[0].Put("a")
	if v := regs[1].Get(); v != "a" {
		t.Fatalf("Get after Put(a) = %q", v)
	}
	regs[2].Put("b")
	for i, r := range regs {
		if v := r.Get(); v != "b" {
			t.Fatalf("replica %d: Get after Put(b) = %q", i+1, v)
		}
	}
}

func TestCluster(t *testing.T) {
	Main()
}

// TestRead reads through read-index on every replica after Puts, on a cluster connected by
// the register's own transport (deliver), which must pass the read-index messages and the
// heartbeats' contexts.
func TestRead(t *testing.T) {
	voters := []uint64{1, 2, 3}
	peers := make(map[uint64]raft.Node)
	storages := make(map[uint64]*Storage)
	for _, id := range voters {
		st := NewStorage(voters)
		peers[id] = raft.RestartNode(&raft.Config{
			ID:              id,
			ElectionTick:    10,
			HeartbeatTick:   1,
			Storage:         st,
			MaxSizePerMsg:   1 << 20,
			MaxInflightMsgs: 256,
			Logger:          quietLogger{},
		})
		storages[id] = st
	}
	send := func(ms []pb.Message) { deliver(peers, ms) }
	stop := make(chan struct{})
	defer func() {
		close(stop)
		for _, nd := range peers {
			nd.Stop()
		}
	}()
	regs := make(map[uint64]*Register)
	for _, id := range voters {
		regs[id] = New(id, peers[id], storages[id], send)
		go func(nd raft.Node) {
			tk := time.NewTicker(5 * time.Millisecond)
			defer tk.Stop()
			for {
				select {
				case <-tk.C:
					nd.Tick()
				case <-stop:
					return
				}
			}
		}(peers[id])
	}
	regs[1].Put("a")
	for _, id := range voters {
		if v := regs[id].Read(); v != "a" {
			t.Fatalf("replica %d: Read after Put(a) = %q", id, v)
		}
	}
	regs[3].Put("b")
	for _, id := range voters {
		if v := regs[id].Read(); v != "b" {
			t.Fatalf("replica %d: Read after Put(b) = %q", id, v)
		}
	}
	if v := regs[2].Get(); v != "b" {
		t.Fatalf("Get after Put(b) = %q", v)
	}
}

func TestDeliverable(t *testing.T) {
	hb := []byte{1, 0, 0, 0, 0, 0, 0, 0}
	cases := []struct {
		m    pb.Message
		want bool
	}{
		{pb.Message{Type: pb.MsgReadIndex, From: 2, To: 1}, true},
		{pb.Message{Type: pb.MsgReadIndex, From: 2, To: 1, Term: 3}, false},
		{pb.Message{Type: pb.MsgReadIndexResp, From: 1, To: 2, Term: 3}, true},
		{pb.Message{Type: pb.MsgHeartbeat, From: 1, To: 2, Term: 3, Context: hb}, true},
		{pb.Message{Type: pb.MsgHeartbeatResp, From: 2, To: 1, Term: 3, Context: hb}, true},
		{pb.Message{Type: pb.MsgVote, From: 2, To: 1, Term: 3, Context: []byte("CampaignTransfer")}, false},
		{pb.Message{Type: pb.MsgApp, From: 1, To: 2, Term: 3}, true},
		{pb.Message{Type: pb.MsgApp, From: 1, To: 1, Term: 3}, false},
	}
	for i, c := range cases {
		if got := deliverable(c.m); got != c.want {
			t.Errorf("case %d: deliverable = %v, want %v", i, got, c.want)
		}
	}
}
