// Package linkv3 is linkv (examples/linkv) over a three-member cluster: three etcd members started
// in-process as examples/putget3 starts them, each serving its raft handler on its own peer
// listener, a client connected to the first member, and linkv's workload (linkv.Check:
// lintest.Run with concurrent clients doing Put and Get of a few keys through that client,
// checked by porcupine against linkv's key-value model). Main panics if porcupine finds the
// history not linearizable; the theorem is that it does not (D20, D21).
//
// The workload is package linkv's (Gen, Apply, Model, Check), imported, so that their proofs
// carry over unchanged. The start of a member is putget3's (startMember), on linkv3's own member
// names, cluster token and ports.
package linkv3

import (
	"net"
	"net/http"

	"github.com/anishathalye/porcupine"
	"go.uber.org/zap"

	"go.etcd.io/etcd/client/pkg/v3/types"
	clientv3 "go.etcd.io/etcd/client/v3"
	"go.etcd.io/etcd/server/v3/config"
	"go.etcd.io/etcd/server/v3/etcdserver"
	"go.etcd.io/etcd/server/v3/etcdserver/api/v3rpc"
	"go.etcd.io/etcd/server/v3/features"

	"github.com/mit-pdos/etcd-grove/examples/linkv"
)

// The members' peer addresses (each member's one peer URL is http://<addr>, served by that
// member's raft handler) and client addresses (only the first is served, to the client: a plain
// host:port, clientv3.New's premise). Not putget's, putget3's or linkv's, so that the examples'
// tests can run at once.
const (
	peerAddr1   = "127.0.0.1:23821"
	peerAddr2   = "127.0.0.1:23822"
	peerAddr3   = "127.0.0.1:23823"
	clientAddr  = "127.0.0.1:23811"
	clientAddr2 = "127.0.0.1:23812"
	clientAddr3 = "127.0.0.1:23813"
)

// startMember starts member name of the new cluster cluster, whose peer URLs are peer (the one
// URL http://peerAddr): the server (configured as putget3's, with linkv3's cluster token), its
// raft handler served on a listener at peerAddr, then the server started.
func startMember(name string, peer types.URLs, peerAddr string, client string,
	cluster types.URLsMap, lg *zap.Logger) (*etcdserver.EtcdServer, error) {
	cfg := config.ServerConfig{
		Name:    name,
		DataDir: name + ".etcd",
		// the three members: a new cluster
		InitialPeerURLsMap:  cluster,
		PeerURLs:            peer,
		ClientURLs:          types.URLs{{Scheme: "http", Host: client}},
		InitialClusterToken: "linkv3",
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
	s.Start()
	return s, nil
}

// Main starts the three members of a new cluster, connects a client to the first and runs
// linkv.Check; it panics if porcupine finds the history illegal. An error from a step before
// Check ends Main without a check (the specs allow every step to fail).
func Main(clients int, ops int) porcupine.CheckResult {
	lg := zap.NewNop()
	peer1 := types.URLs{{Scheme: "http", Host: peerAddr1}}
	peer2 := types.URLs{{Scheme: "http", Host: peerAddr2}}
	peer3 := types.URLs{{Scheme: "http", Host: peerAddr3}}
	cluster := types.URLsMap{"linkv3-1": peer1, "linkv3-2": peer2, "linkv3-3": peer3}

	s, err := startMember("linkv3-1", peer1, peerAddr1, clientAddr, cluster, lg)
	if err != nil {
		return porcupine.Unknown
	}
	if _, err := startMember("linkv3-2", peer2, peerAddr2, clientAddr2, cluster, lg); err != nil {
		return porcupine.Unknown
	}
	if _, err := startMember("linkv3-3", peer3, peerAddr3, clientAddr3, cluster, lg); err != nil {
		return porcupine.Unknown
	}

	gs := v3rpc.Server(s, nil, nil)
	l, err := net.Listen("tcp", clientAddr)
	if err != nil {
		return porcupine.Unknown
	}
	go gs.Serve(l)

	// etcd's default client configuration (its default retries): the members never answer with a
	// refusal (authentication off, voters), so a Put is sent at most once and the cluster applies it
	// at most once, while a read may be retried (decision D29).
	cli, err := clientv3.New(clientv3.Config{
		Endpoints: []string{clientAddr},
		Logger:    lg,
	})
	if err != nil {
		return porcupine.Unknown
	}
	r := linkv.Check(cli, clients, ops, 0)
	if r == porcupine.Illegal {
		panic("linkv3: porcupine found the history not linearizable")
	}
	return r
}
