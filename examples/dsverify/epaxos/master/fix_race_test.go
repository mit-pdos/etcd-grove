package master

import (
	"errors"
	"net"
	"net/http"
	"net/rpc"
	"strconv"
	"strings"
	"sync/atomic"
	"testing"
	"time"

	"github.com/imdea-software/swiftpaxos-epaxos/config"
	"github.com/imdea-software/swiftpaxos-epaxos/dlog"
	"github.com/imdea-software/swiftpaxos-epaxos/replica/defs"
)

// fakeReplica serves Replica.Ping and Replica.BeTheLeader as a replica's rpc server does;
// replica 0's Ping fails (a broken connection, a slow replica: the master then moves the
// leader).
type fakeReplica struct {
	id    int
	pings *int32
}

func (f *fakeReplica) Ping(args *defs.PingArgs, reply *defs.PingReply) error {
	atomic.AddInt32(f.pings, 1)
	if f.id == 0 {
		return errors.New("replica 0 is down")
	}
	return nil
}

func (f *fakeReplica) BeTheLeader(args *defs.BeTheLeaderArgs, reply *defs.BeTheLeaderReply) error {
	return nil
}

// TestPingConcurrentWithRegister runs the master's run loop against five rpc servers while
// replica 0 calls Register again (as a replica does after a failed call). The ping rounds
// (pingNode) and the leader changes (beTheLeader) write master.leader and master.alive, which
// Register reads and writes under master.lock: under -race this must report no data race (M1).
func TestPingConcurrentWithRegister(t *testing.T) {
	m := New(5, 7001, &config.Config{Proxy: &config.ProxyInfo{}}, &dlog.Logger{})
	var pings0 int32
	var args []*defs.RegisterArgs
	for i := 0; i < 5; i++ {
		var pings int32
		f := &fakeReplica{id: i, pings: &pings}
		if i == 0 {
			f.pings = &pings0
		}
		srv := rpc.NewServer()
		if err := srv.RegisterName("Replica", f); err != nil {
			t.Fatal(err)
		}
		l, err := net.Listen("tcp", "127.0.0.1:0")
		if err != nil {
			t.Fatal(err)
		}
		defer l.Close()
		go http.Serve(l, srv)
		port, _ := strconv.Atoi(strings.Split(l.Addr().String(), ":")[1])
		// the master dials Addr:(Port+1000), a replica's rpc port
		args = append(args, &defs.RegisterArgs{Addr: "127.0.0.1", Port: port - 1000})
	}
	for round := 0; round < 2; round++ {
		for _, a := range args {
			var reply defs.RegisterReply
			m.Register(a, &reply)
		}
	}
	go m.run()

	// Replica 0 calls Register again and again, from the master's dial loop to two ping rounds
	// after the first (which runs under the lock); GetReplicaList and GetLeader meanwhile.
	stop := make(chan bool)
	stopped := make(chan error)
	go func() {
		for {
			select {
			case <-stop:
				stopped <- nil
				return
			default:
			}
			var reply defs.RegisterReply
			if err := m.Register(args[0], &reply); err != nil || !reply.Ready {
				<-stop
				stopped <- errors.New("Register failed")
				return
			}
			var leader defs.GetLeaderReply
			m.GetLeader(&defs.GetLeaderArgs{}, &leader)
			time.Sleep(10 * time.Millisecond)
		}
	}()
	for atomic.LoadInt32(&pings0) < 3 {
		var list defs.GetReplicaListReply
		m.GetReplicaList(&defs.GetReplicaListArgs{}, &list)
		time.Sleep(10 * time.Millisecond)
	}
	stop <- true
	if err := <-stopped; err != nil {
		t.Fatal(err)
	}
}
