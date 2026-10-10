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
