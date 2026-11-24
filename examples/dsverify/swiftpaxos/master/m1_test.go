package master

import (
	"net"
	"net/http"
	"net/rpc"
	"testing"
	"time"

	"github.com/imdea-software/swiftpaxos/config"
	"github.com/imdea-software/swiftpaxos/dlog"
	"github.com/imdea-software/swiftpaxos/replica/defs"
)

type fakeReplica struct{}

func (*fakeReplica) Ping(_ *defs.PingArgs, _ *defs.PingReply) error { return nil }

func (*fakeReplica) BeTheLeader(_ *defs.BeTheLeaderArgs, reply *defs.BeTheLeaderReply) error {
	reply.Leader, reply.NextLeader = -1, -1
	return nil
}

// M1: master.run's pings write alive (and leader) while the rpc methods
// (GetReplicaList, GetLeader: every client's Connect) read them under the
// lock. Run with -race: the race detector fails the test on a data race.
func TestIssueM1_PingsVsRPCs(t *testing.T) {
	l, err := net.Listen("tcp", "127.0.0.1:0")
	if err != nil {
		t.Fatal(err)
	}
	defer l.Close()
	srv := rpc.NewServer()
	srv.RegisterName("Replica", &fakeReplica{})
	go http.Serve(l, srv)

	m := New(1, 7001, &config.Config{}, &dlog.Logger{})
	port := l.Addr().(*net.TCPAddr).Port - 1000 // the master dials port + 1000
	for _, want := range []bool{true, true} {
		var reply defs.RegisterReply
		if err := m.Register(&defs.RegisterArgs{Addr: "127.0.0.1", Port: port}, &reply); err != nil || reply.Ready != want {
			t.Fatalf("Register: %v %+v", err, reply)
		}
	}
	go m.run()

	// The first ping round ends at about 3 s, the second at about 6 s.
	deadline := time.Now().Add(7500 * time.Millisecond)
	for time.Now().Before(deadline) {
		var rl defs.GetReplicaListReply
		if err := m.GetReplicaList(&defs.GetReplicaListArgs{}, &rl); err != nil || !rl.Ready || !rl.AliveList[0] {
			t.Fatalf("GetReplicaList: %v %+v", err, rl)
		}
		var gl defs.GetLeaderReply
		if err := m.GetLeader(&defs.GetLeaderArgs{}, &gl); err != nil || gl.LeaderId != 0 {
			t.Fatalf("GetLeader: %v %+v", err, gl)
		}
		time.Sleep(10 * time.Millisecond)
	}
}
