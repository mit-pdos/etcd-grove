// Package auth3 is authkv (examples/etcd/auth) with a three-member cluster (notes/auth3-scope.md,
// variant A1): three etcd members started in-process with auth on (the simple token provider,
// etcd's default token TTL), each serving its raft handler on its own peer listener, as putget3's
// members do, then, through the first member only, authkv's run: its gRPC API served, the auth
// state set up and auth enabled, the four principals' workloads, the history check and u's watch
// check (auth.Run). Every client is a client of the first member, the only one serving gRPC; the
// other two apply every entry, the auth set-up's and the Authenticate entries included, with auth
// on. Main panics if the first member let a principal do what the auth state does not permit; the
// theorem to prove is that it does not.
//
// The members take the examples' no-snapshot settings (etcdstart.NoSnapCount, NoSnapCatchUp): a
// leader never sends a follower a snapshot.
package auth3

import (
	"net"
	"net/http"

	"go.uber.org/zap"

	"go.etcd.io/etcd/client/pkg/v3/types"
	"go.etcd.io/etcd/server/v3/config"
	"go.etcd.io/etcd/server/v3/etcdserver"
	"go.etcd.io/etcd/server/v3/features"

	"github.com/mit-pdos/etcd-grove/examples/etcd/auth"
	"github.com/mit-pdos/etcd-grove/examples/lib/etcdstart"
)

// The members' peer addresses (each member's one peer URL is http://<addr>, served by that
// member's raft handler) and client addresses (only the first is served: a plain host:port), not
// any other example's, so that the examples' tests can run at once.
const (
	peerAddr1   = "127.0.0.1:24131"
	peerAddr2   = "127.0.0.1:24132"
	peerAddr3   = "127.0.0.1:24133"
	clientAddr  = "127.0.0.1:24141"
	clientAddr2 = "127.0.0.1:24142"
	clientAddr3 = "127.0.0.1:24143"
)

// startMember starts member name of the new cluster whose initial members' peer URLs are cluster
// (token auth3), with auth's configuration (authkv's startServer: the simple token provider and
// etcd's default token TTL, 300 seconds), its peer URLs peer (the one URL http://peerAddr), its one
// client URL http://client and the examples' no-snapshot settings; it serves the member's raft
// handler on a listener at peerAddr (etcdstart.NewMember's), then starts the member.
func startMember(name string, peer types.URLs, peerAddr string, client string, cluster types.URLsMap,
	lg *zap.Logger) (*etcdserver.EtcdServer, error) {
	cfg := config.ServerConfig{
		Name:                   name,
		DataDir:                name + ".etcd",
		InitialPeerURLsMap:     cluster,
		PeerURLs:               peer,
		ClientURLs:             types.URLs{{Scheme: "http", Host: client}},
		InitialClusterToken:    "auth3",
		NewCluster:             true,
		TickMs:                 100,
		ElectionTicks:          10,
		SnapshotCount:          etcdstart.NoSnapCount,
		SnapshotCatchUpEntries: etcdstart.NoSnapCatchUp,
		MaxTxnOps:              128,
		MaxRequestBytes:        1536 * 1024,
		AuthToken:              "simple",
		TokenTTL:               300,
		Logger:                 lg,
		ServerFeatureGate:      features.NewDefaultServerFeatureGate(name, lg),
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

// Main starts the three members of a new cluster with auth on, then runs authkv's set-up,
// workloads and checks through the first (auth.Run), and returns its result (auth.Ok,
// auth.Failed, auth.WatchEnded); a member that fails to start ends Main with auth.Failed.
func Main() int {
	lg := zap.NewNop()
	peer1 := types.URLs{{Scheme: "http", Host: peerAddr1}}
	peer2 := types.URLs{{Scheme: "http", Host: peerAddr2}}
	peer3 := types.URLs{{Scheme: "http", Host: peerAddr3}}
	cluster := types.URLsMap{"auth3-1": peer1, "auth3-2": peer2, "auth3-3": peer3}

	s, err := startMember("auth3-1", peer1, peerAddr1, clientAddr, cluster, lg)
	if err != nil {
		return auth.Failed
	}
	if _, err := startMember("auth3-2", peer2, peerAddr2, clientAddr2, cluster, lg); err != nil {
		return auth.Failed
	}
	if _, err := startMember("auth3-3", peer3, peerAddr3, clientAddr3, cluster, lg); err != nil {
		return auth.Failed
	}
	return auth.Run(s, clientAddr, lg)
}
