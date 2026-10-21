// Package linkv3p is linkv3 (examples/linkv3) under network partitions: three etcd members started
// in-process as examples/putget3 starts them, each serving its raft handler on its own peer
// listener and etcd's gRPC API on its own client listener, a client connected to each member,
// a partitioner goroutine that cuts and mends the links between members, and between each client
// and its member, on a schedule Main is given, and linkvtxn's workload (lintest.Run with concurrent clients doing gets, lists, puts,
// deletes, multi-operation transactions and compare-and-sets of a few keys, robustness's KV
// traffic without leases and stale reads, each operation through a member picked at random,
// checked by porcupine against linkvtxn's model of etcd's KV; notes/linkv3p-txn-plan.md). Main
// panics if porcupine finds the history not linearizable; the theorem is that it does not, for
// every schedule (notes/partition-plan.md, notes/client-cut-plan.md).
//
// The partitions are etcd's own: EtcdServer.CutPeer and MendPeer, which etcd's integration tests
// use (tests/framework/integration/cluster.go, InjectPartition/RecoverPartition), pause and
// resume the transport's peer, which then drops every message to and from it. Both directions of
// a link are cut and mended together, as those tests do.
//
// The cuts between a client and its member are etcd's own too: each client reaches its member
// through a copy of etcd's integration tests' bridge (third_party/bridge, the TCP proxy of
// ClusterConfig.UseBridge), whose Blackhole drops every byte both ways until Unblackhole closes
// the proxied connections, and whose DropConnections closes them. A client recovers by itself:
// its calls wait for a connection (clientv3's default WaitForReady), and gRPC re-dials the bridge.
//
// The workload is package linkvtxn's (Gen, Apply, Model), imported, so that their proofs carry
// over unchanged; Apply here picks the member. (Until 2026-10-20 it was package linkv's, Puts and
// Gets only.) The start of a member is putget3's (startMember), on
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

	"github.com/mit-pdos/etcd-grove/examples/linkvtxn"
	"github.com/mit-pdos/etcd-grove/examples/lintest"
	"github.com/mit-pdos/etcd-grove/third_party/bridge"
)

// The members' peer addresses (each member's one peer URL is http://<addr>, served by that
// member's raft handler), client addresses (each served by the member's gRPC server) and bridge
// addresses (each the bridge to a member's client address, which its client dials: a plain
// host:port, clientv3.New's premise). Not another example's, so that the examples' tests can run
// at once.
const (
	peerAddr1   = "127.0.0.1:23841"
	peerAddr2   = "127.0.0.1:23842"
	peerAddr3   = "127.0.0.1:23843"
	clientAddr1 = "127.0.0.1:23831"
	clientAddr2 = "127.0.0.1:23832"
	clientAddr3 = "127.0.0.1:23833"
	bridgeAddr1 = "127.0.0.1:23851"
	bridgeAddr2 = "127.0.0.1:23852"
	bridgeAddr3 = "127.0.0.1:23853"
)

// The kinds of a schedule's step.
const (
	// cut the link between members A and B, both directions (CutPeer)
	PeerCut = 0
	// mend it (MendPeer)
	PeerMend = 1
	// cut member A's client off it: every byte between them dropped (the bridge's Blackhole)
	ClientBlackhole = 2
	// end that: the bridge's connections closed, new ones forwarded (Unblackhole)
	ClientUnblackhole = 3
	// close the connections between member A and its client (the bridge's DropConnections)
	ClientDrop = 4
)

// A Step of a partition schedule: after Delay, its Kind's action on members A and B (indices into
// Main's members, 0 to 2): a peer step cuts or mends the link between A and B in both directions;
// a client step acts on the link between member A and its client (B unused). A step whose
// indices are out of range (or equal, for a peer step), or whose kind is none of the above, does
// nothing.
type Step struct {
	Delay time.Duration
	Kind  int
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

// startBridge starts a bridge at addr to the member's client address client: the listener, then
// the bridge's accept loop (bridge.New).
func startBridge(addr string, client string) (bridge.Bridge, error) {
	l, err := net.Listen("tcp", addr)
	if err != nil {
		return nil, err
	}
	return bridge.New(client, l), nil
}

// peerStep applies a peer step to the members srvs: cuts or mends the link between members a and
// b in both directions (etcd's CutPeer/MendPeer, as its integration tests'
// InjectPartition/RecoverPartition).
func peerStep(srvs []*etcdserver.EtcdServer, kind int, a int, b int) {
	if a < 0 || a >= len(srvs) || b < 0 || b >= len(srvs) || a == b {
		return
	}
	sa := srvs[a]
	sb := srvs[b]
	if kind == PeerCut {
		sa.CutPeer(sb.MemberID())
		sb.CutPeer(sa.MemberID())
	} else {
		sa.MendPeer(sb.MemberID())
		sb.MendPeer(sa.MemberID())
	}
}

// clientStep applies a client step to member a's bridge (brs[a]), as etcd's integration tests
// do (Member.Bridge().Blackhole(), ...); holed[a] says whether that bridge is blackholed. A
// blackhole of a blackholed bridge does nothing: the bridge's Blackhole closes its channel
// unguarded, so a second one would panic (issues/etcd-bridge-blackhole-twice-panic.md).
func clientStep(brs []bridge.Bridge, holed []bool, kind int, a int) {
	if a < 0 || a >= len(brs) {
		return
	}
	br := brs[a]
	if kind == ClientBlackhole {
		if !holed[a] {
			br.Blackhole()
			holed[a] = true
		}
	} else if kind == ClientUnblackhole {
		br.Unblackhole()
		holed[a] = false
	} else {
		br.DropConnections()
	}
}

// partitioner applies the schedule sched to the members srvs and their bridges brs: each step,
// after its delay.
func partitioner(srvs []*etcdserver.EtcdServer, brs []bridge.Bridge, sched []Step) {
	holed := make([]bool, len(brs))
	for _, st := range sched {
		time.Sleep(st.Delay)
		if st.Kind == PeerCut || st.Kind == PeerMend {
			peerStep(srvs, st.Kind, st.A, st.B)
		} else if st.Kind == ClientBlackhole || st.Kind == ClientUnblackhole || st.Kind == ClientDrop {
			clientStep(brs, holed, st.Kind, st.A)
		}
	}
}

// Apply runs one operation through a client of clis picked at random (linkvtxn.Apply).
func Apply(clis []*clientv3.Client, input any) any {
	i := primitive.RandomUint64() % uint64(len(clis))
	return linkvtxn.Apply(clis[i], input)
}

// Check runs lintest.Run of clients concurrent clients, each running ops operations through the
// clients clis (one per member, each operation's picked at random), and returns porcupine's
// verdict against linkvtxn's model.
func Check(clis []*clientv3.Client, clients int, ops int, timeout time.Duration) porcupine.CheckResult {
	apply := func(input any) any { return Apply(clis, input) }
	return lintest.Run(linkvtxn.Model(), apply, linkvtxn.Gen, lintest.CounterClock(), clients, ops,
		timeout)
}

// newClient connects a one-attempt client to the member (through its bridge) at addr: a write is sent at most once, so
// the cluster applies it at most once (decision D21i).
func newClient(addr string, lg *zap.Logger) (*clientv3.Client, error) {
	return clientv3.New(clientv3.Config{
		Endpoints:       []string{addr},
		Logger:          lg,
		MaxUnaryRetries: 1,
	})
}

// Main starts the three members of a new cluster, a bridge to each member's client address,
// connects a client to each bridge, starts the partitioner on sched and runs Check; it panics if porcupine finds the history illegal. An
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

	br1, err := startBridge(bridgeAddr1, clientAddr1)
	if err != nil {
		return porcupine.Unknown
	}
	br2, err := startBridge(bridgeAddr2, clientAddr2)
	if err != nil {
		return porcupine.Unknown
	}
	br3, err := startBridge(bridgeAddr3, clientAddr3)
	if err != nil {
		return porcupine.Unknown
	}
	brs := []bridge.Bridge{br1, br2, br3}

	cli1, err := newClient(bridgeAddr1, lg)
	if err != nil {
		return porcupine.Unknown
	}
	cli2, err := newClient(bridgeAddr2, lg)
	if err != nil {
		return porcupine.Unknown
	}
	cli3, err := newClient(bridgeAddr3, lg)
	if err != nil {
		return porcupine.Unknown
	}
	clis := []*clientv3.Client{cli1, cli2, cli3}

	go partitioner(srvs, brs, sched)
	r := Check(clis, clients, ops, 0)
	if r == porcupine.Illegal {
		panic("linkv3p: porcupine found the history not linearizable")
	}
	return r
}
