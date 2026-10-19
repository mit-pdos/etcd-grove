// Package putget3 is putget (examples/putget) with a three-member cluster: three etcd members
// started in-process, each serving its raft handler on its own peer listener, a client connected
// to the first member, a Put of a key and a Get of the same key, and a check that the Get returns
// the Put's value (D21 stage M5, notes/decisions.md). Main panics if the check fails; the adequacy
// theorem is that it does not.
//
// Main calls what putget calls, per member (etcdserver.NewServer over bootstrap's contract,
// (*EtcdServer).Start, net.Listen), plus each member's raft handler served on its peer URL's
// listener ((*EtcdServer).RaftHandler, http.Serve on a goroutine), then, for the first member
// only, what putget does: v3rpc.Server, net.Listen, (*grpc.Server).Serve on a goroutine,
// clientv3.New (one endpoint), the client's Put and Get. An error from any step ends Main
// without a check, as in putget.
package putget3

import (
	"context"
	"net"
	"net/http"

	"go.uber.org/zap"

	"go.etcd.io/etcd/client/pkg/v3/types"
	clientv3 "go.etcd.io/etcd/client/v3"
	"go.etcd.io/etcd/server/v3/config"
	"go.etcd.io/etcd/server/v3/etcdserver"
	"go.etcd.io/etcd/server/v3/etcdserver/api/v3rpc"
	"go.etcd.io/etcd/server/v3/features"
)

// The members' peer addresses (each member's one peer URL is http://<addr>, served by that
// member's raft handler) and client addresses (only the first is served, to the client: a plain
// host:port, as in putget).
const (
	peerAddr1   = "127.0.0.1:23801"
	peerAddr2   = "127.0.0.1:23802"
	peerAddr3   = "127.0.0.1:23803"
	clientAddr  = "127.0.0.1:23791"
	clientAddr2 = "127.0.0.1:23792"
	clientAddr3 = "127.0.0.1:23793"
)

// startMember starts member name of the new cluster cluster, whose peer URLs are peer (the one
// URL http://peerAddr): the server (configured as putget's), its raft handler served on a
// listener at peerAddr, then the server started.
func startMember(name string, peer types.URLs, peerAddr string, client string,
	cluster types.URLsMap, lg *zap.Logger) (*etcdserver.EtcdServer, error) {
	cfg := config.ServerConfig{
		Name:    name,
		DataDir: name + ".etcd",
		// the three members: a new cluster
		InitialPeerURLsMap:  cluster,
		PeerURLs:            peer,
		ClientURLs:          types.URLs{{Scheme: "http", Host: client}},
		InitialClusterToken: "putget3",
		NewCluster:          true,
		// as putget: raft's clock, etcd's default snapshot count, the catch-up entries past
		// the theorem's step bound (NewServer's run bound, D21 M3), etcd's default request
		// limits
		TickMs:                 100,
		ElectionTicks:          10,
		SnapshotCount:          etcdserver.DefaultSnapshotCount,
		SnapshotCatchUpEntries: 1 << 48,
		MaxTxnOps:              128,
		MaxRequestBytes:        1536 * 1024,
		// NewServer's premises, as putget
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

// Main starts the three members of a new cluster, puts key "k" with value "v" through the first,
// gets "k" from it and panics if the value is not "v".
func Main() {
	lg := zap.NewNop()
	peer1 := types.URLs{{Scheme: "http", Host: peerAddr1}}
	peer2 := types.URLs{{Scheme: "http", Host: peerAddr2}}
	peer3 := types.URLs{{Scheme: "http", Host: peerAddr3}}
	cluster := types.URLsMap{"putget3-1": peer1, "putget3-2": peer2, "putget3-3": peer3}

	s, err := startMember("putget3-1", peer1, peerAddr1, clientAddr, cluster, lg)
	if err != nil {
		return
	}
	if _, err := startMember("putget3-2", peer2, peerAddr2, clientAddr2, cluster, lg); err != nil {
		return
	}
	if _, err := startMember("putget3-3", peer3, peerAddr3, clientAddr3, cluster, lg); err != nil {
		return
	}

	gs := v3rpc.Server(s, nil, nil)
	l, err := net.Listen("tcp", clientAddr)
	if err != nil {
		return
	}
	go gs.Serve(l)

	cli, err := clientv3.New(clientv3.Config{
		Endpoints: []string{clientAddr},
		Logger:    lg,
	})
	if err != nil {
		return
	}
	ctx := context.Background()
	if _, err := cli.Put(ctx, "k", "v"); err != nil {
		return
	}
	resp, err := cli.Get(ctx, "k")
	if err != nil {
		return
	}
	if len(resp.Kvs) == 0 || string(resp.Kvs[0].Value) != "v" {
		panic("putget3: Get did not return the Put's value")
	}
}
