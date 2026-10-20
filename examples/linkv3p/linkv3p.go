// Package linkv3p is linkv3 (examples/linkv3) under network partitions: three etcd members started
// in-process as examples/putget3 starts them, each serving its raft handler on its own peer
// listener and etcd's gRPC API on its own client listener, a client connected to each member,
// a partitioner goroutine that cuts and mends the links between members on a schedule Main is
// given, and linkv's workload (lintest.Run with concurrent clients doing Put and Get of a few
// keys, each operation through a member picked at random, checked by porcupine against linkv's
// key-value model). Main panics if porcupine finds the history not linearizable; the theorem is
// that it does not, for every schedule (notes/partition-plan.md).
//
// The partitions are etcd's own: EtcdServer.CutPeer and MendPeer, which etcd's integration tests
// use (tests/framework/integration/cluster.go, InjectPartition/RecoverPartition), pause and
// resume the transport's peer, which then drops every message to and from it. Both directions of
// a link are cut and mended together, as those tests do.
//
// The workload is package linkv's (Gen, Apply, Model), imported, so that their proofs carry over
// unchanged; Apply here picks the member. The start of a member is putget3's (startMember), on
// linkv3p's own member names, cluster token and ports, plus the member's gRPC server.
package linkv3p

import (
	"net"
	"net/http"
	"time"

	"github.com/anishathalye/porcupine"
	"github.com/goose-lang/primitive"
	"go.uber.org/zap"

	"go.etcd.io/etcd/client/pkg/v3/types"
	clientv3 "go.etcd.io/etcd/client/v3"
	"go.etcd.io/etcd/server/v3/config"
	"go.etcd.io/etcd/server/v3/etcdserver"
	"go.etcd.io/etcd/server/v3/etcdserver/api/v3rpc"
	"go.etcd.io/etcd/server/v3/features"

	"github.com/mit-pdos/etcd-grove/examples/linkv"
	"github.com/mit-pdos/etcd-grove/examples/lintest"
)

// The members' peer addresses (each member's one peer URL is http://<addr>, served by that
// member's raft handler) and client addresses (each served by the member's gRPC server, to its
// client: a plain host:port, clientv3.New's premise). Not another example's, so that the
// examples' tests can run at once.
const (
	peerAddr1   = "127.0.0.1:23841"
	peerAddr2   = "127.0.0.1:23842"
	peerAddr3   = "127.0.0.1:23843"
	clientAddr1 = "127.0.0.1:23831"
	clientAddr2 = "127.0.0.1:23832"
	clientAddr3 = "127.0.0.1:23833"
)

// A Step of a partition schedule: after Delay, cut (Cut) or mend the link between members A and
// B (indices into Main's members, 0 to 2), in both directions. A step whose indices are out of
// range or equal does nothing.
type Step struct {
	Delay time.Duration
	Cut   bool
	A     int
	B     int
}

// startMember starts member name of the new cluster cluster, whose peer URLs are peer (the one
// URL http://peerAddr): the server (configured as putget3's, with linkv3p's cluster token), its
// raft handler served on a listener at peerAddr, the server started, and its gRPC server served
// on a listener at client.
func startMember(name string, peer types.URLs, peerAddr string, client string,
	cluster types.URLsMap, lg *zap.Logger) (*etcdserver.EtcdServer, error) {
	cfg := config.ServerConfig{
		Name:    name,
		DataDir: name + ".etcd",
		// the three members: a new cluster
		InitialPeerURLsMap:  cluster,
		PeerURLs:            peer,
		ClientURLs:          types.URLs{{Scheme: "http", Host: client}},
		InitialClusterToken: "linkv3p",
		NewCluster:          true,
		// as putget3: raft's clock, etcd's default snapshot count, the catch-up entries past
		// the theorem's step bound (NewServer's run bound, D21 M3), etcd's default request
		// limits
		TickMs:                 100,
		ElectionTicks:          10,
		SnapshotCount:          etcdserver.DefaultSnapshotCount,
		SnapshotCatchUpEntries: 1 << 48,
		MaxTxnOps:              128,
		MaxRequestBytes:        1536 * 1024,
		// NewServer's premises, as putget3
		Logger:            lg,
		ServerFeatureGate: features.NewDefaultServerFeatureGate(name, lg),
	}
	s, err := etcdserver.NewServer(cfg)
	if err != nil {
		return nil, err
	}
	// the member's peer URL is served by its own transport (D21b's deployment fact)
	l, err := net.Listen("tcp", peerAddr)
	if err != nil {
		return nil, err
	}
	go http.Serve(l, s.RaftHandler())
	// the member's client address, before the server starts (an error leaves nothing running)
	cl, err := net.Listen("tcp", client)
	if err != nil {
		return nil, err
	}
	s.Start()
	gs := v3rpc.Server(s, nil, nil)
	go gs.Serve(cl)
	return s, nil
}

// partitioner applies the schedule sched to the members srvs: for each step, after its delay,
// cuts or mends the link between its two members in both directions (etcd's CutPeer/MendPeer,
// as its integration tests' InjectPartition/RecoverPartition).
func partitioner(srvs []*etcdserver.EtcdServer, sched []Step) {
	for _, st := range sched {
		time.Sleep(st.Delay)
		if st.A < 0 || st.A >= len(srvs) || st.B < 0 || st.B >= len(srvs) || st.A == st.B {
			continue
		}
		a := srvs[st.A]
		b := srvs[st.B]
		if st.Cut {
			a.CutPeer(b.MemberID())
			b.CutPeer(a.MemberID())
		} else {
			a.MendPeer(b.MemberID())
			b.MendPeer(a.MemberID())
		}
	}
}

// Apply runs one operation through a client of clis picked at random (linkv.Apply).
func Apply(clis []*clientv3.Client, input any) any {
	i := primitive.RandomUint64() % uint64(len(clis))
	return linkv.Apply(clis[i], input)
}

// Check runs lintest.Run of clients concurrent clients, each running ops operations through the
// clients clis (one per member, each operation's picked at random), and returns porcupine's
// verdict against linkv's model.
func Check(clis []*clientv3.Client, clients int, ops int, timeout time.Duration) porcupine.CheckResult {
	apply := func(input any) any { return Apply(clis, input) }
	return lintest.Run(linkv.Model(), apply, linkv.Gen, lintest.CounterClock(), clients, ops, timeout)
}

// newClient connects a one-attempt client to the member at addr: a Put is sent at most once, so
// the cluster applies it at most once (decision D21i).
func newClient(addr string, lg *zap.Logger) (*clientv3.Client, error) {
	return clientv3.New(clientv3.Config{
		Endpoints:       []string{addr},
		Logger:          lg,
		MaxUnaryRetries: 1,
	})
}

// Main starts the three members of a new cluster, connects a client to each, starts the
// partitioner on sched and runs Check; it panics if porcupine finds the history illegal. An
// error from a step before Check ends Main without a check (the specs allow every step to fail).
func Main(clients int, ops int, sched []Step) porcupine.CheckResult {
	lg := zap.NewNop()
	peer1 := types.URLs{{Scheme: "http", Host: peerAddr1}}
	peer2 := types.URLs{{Scheme: "http", Host: peerAddr2}}
	peer3 := types.URLs{{Scheme: "http", Host: peerAddr3}}
	cluster := types.URLsMap{"linkv3p-1": peer1, "linkv3p-2": peer2, "linkv3p-3": peer3}

	s1, err := startMember("linkv3p-1", peer1, peerAddr1, clientAddr1, cluster, lg)
	if err != nil {
		return porcupine.Unknown
	}
	s2, err := startMember("linkv3p-2", peer2, peerAddr2, clientAddr2, cluster, lg)
	if err != nil {
		return porcupine.Unknown
	}
	s3, err := startMember("linkv3p-3", peer3, peerAddr3, clientAddr3, cluster, lg)
	if err != nil {
		return porcupine.Unknown
	}
	srvs := []*etcdserver.EtcdServer{s1, s2, s3}

	cli1, err := newClient(clientAddr1, lg)
	if err != nil {
		return porcupine.Unknown
	}
	cli2, err := newClient(clientAddr2, lg)
	if err != nil {
		return porcupine.Unknown
	}
	cli3, err := newClient(clientAddr3, lg)
	if err != nil {
		return porcupine.Unknown
	}
	clis := []*clientv3.Client{cli1, cli2, cli3}

	go partitioner(srvs, sched)
	r := Check(clis, clients, ops, 0)
	if r == porcupine.Illegal {
		panic("linkv3p: porcupine found the history not linearizable")
	}
	return r
}
