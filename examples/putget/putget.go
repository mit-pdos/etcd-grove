// Package putget is the adequacy example of etcd's server and client: one etcd member started
// in-process, a client connected to it, a Put of a key and a Get of the same key, and a check
// that the Get returns the Put's value (open-work item 9, notes/STATUS.md). Main panics if the
// check fails; the adequacy theorem to prove is that it does not (not proved yet: notes/STATUS.md,
// "Item 9: the adequacy example", and notes/decisions.md, D19).
//
// Main calls only what the proofs specify: etcdserver.NewServer (over bootstrap's contract),
// (*EtcdServer).Start, v3rpc.Server, net.Listen, (*grpc.Server).Serve on a goroutine,
// clientv3.New, the client's Put and Get. The configuration meets NewServer's and New's premises
// (see the comments on each field). An error from any step ends Main without a check: the specs
// allow every step to fail (no leader in time, a dial error, ...), and the conclusion is about
// the Get's value when both succeed.
package putget

import (
	"context"
	"net"

	"go.uber.org/zap"

	"go.etcd.io/etcd/client/pkg/v3/types"
	clientv3 "go.etcd.io/etcd/client/v3"
	"go.etcd.io/etcd/server/v3/config"
	"go.etcd.io/etcd/server/v3/etcdserver"
	"go.etcd.io/etcd/server/v3/etcdserver/api/v3rpc"
	"go.etcd.io/etcd/server/v3/features"
)

// The client address: the string net.Listen is given is the client's endpoint, verbatim (a plain
// host:port, no scheme: clientv3.New's premise plainEndpoint).
const clientAddr = "127.0.0.1:23790"

// Main starts one member of a new cluster, puts key "k" with value "v", gets "k" and panics if the
// value is not "v".
func Main() {
	lg := zap.NewNop()
	peer := types.URLs{{Scheme: "http", Host: "127.0.0.1:23800"}}
	cfg := config.ServerConfig{
		Name:    "putget",
		DataDir: "putget.etcd",
		// one member, this one: a new cluster
		InitialPeerURLsMap:  types.URLsMap{"putget": peer},
		PeerURLs:            peer,
		ClientURLs:          types.URLs{{Scheme: "http", Host: clientAddr}},
		InitialClusterToken: "putget",
		NewCluster:          true,
		// raft's clock (a positive tick: the raft node's ticker)
		TickMs:        100,
		ElectionTicks: 10,
		// etcd's default snapshot count; the catch-up entries past the theorem's step bound
		// (NewServer's run bound, D21 M3: receiptBound <= SnapshotCatchUpEntries + 1, so raft's
		// log is compacted at index 1 only and its leader sends no snapshot), etcd's default
		// request limits
		SnapshotCount:          etcdserver.DefaultSnapshotCount,
		SnapshotCatchUpEntries: 1 << 48,
		MaxTxnOps:              128,
		MaxRequestBytes:        1536 * 1024,
		// NewServer's premises: a logger, the compactor off (AutoCompactionRetention zero),
		// pre-vote off (PreVote false, its zero value), a non-negative compaction batch limit
		// (zero), the server's feature gate (a *featuregate.featureGate)
		Logger:            lg,
		ServerFeatureGate: features.NewDefaultServerFeatureGate("putget", lg),
	}
	s, err := etcdserver.NewServer(cfg)
	if err != nil {
		return
	}
	s.Start()

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
		panic("putget: Get did not return the Put's value")
	}
}
