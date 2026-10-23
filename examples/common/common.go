// Package common is the examples' shared start of etcd: a member's configuration and server, its
// gRPC service on a listener, and a client of one address. Each function is what several examples
// did, verbatim, with what differed among them (the member's name, its addresses, the cluster's
// map and token) as parameters, so that it is translated and proved once
// (Proof/github_com/mit_pdos/etcd_grove/examples/common/).
//
// Every function calls only what the proofs specify: etcdserver.NewServer (over bootstrap's
// contract), (*EtcdServer).Start, (*EtcdServer).RaftHandler, http.Serve and (*grpc.Server).Serve
// on goroutines, v3rpc.Server, net.Listen, clientv3.New. An error from a step is returned; the
// specs allow every step to fail.
package common

import (
	"net"
	"net/http"
	"time"

	"go.uber.org/zap"
	"google.golang.org/grpc"
	"google.golang.org/grpc/keepalive"

	"go.etcd.io/etcd/client/pkg/v3/types"
	clientv3 "go.etcd.io/etcd/client/v3"
	"go.etcd.io/etcd/server/v3/config"
	"go.etcd.io/etcd/server/v3/etcdserver"
	"go.etcd.io/etcd/server/v3/etcdserver/api/v3rpc"
	"go.etcd.io/etcd/server/v3/features"
)

// The clients' timeouts, etcdctl's defaults (etcdctl/ctlv3/ctl.go; notes/client-timeouts-plan.md):
// the dial timeout; the timeout of one request (etcdctl's --command-timeout), in which every unary
// call of the examples is made (context.WithTimeout(context.Background(), RequestTimeout), the
// context cancelled after the call, as client/v3's documentation shows); and gRPC keepalive, a
// ping every KeepAliveTime of no reads (grpc raises it to its 10s floor), the connection closed
// when a ping is not answered within KeepAliveTimeout, so that a silently cut member's calls fail
// and the balancer moves on (notes/keepalive-plan.md).
const (
	DialTimeout      = 2 * time.Second
	RequestTimeout   = 5 * time.Second
	KeepAliveTime    = 2 * time.Second
	KeepAliveTimeout = 6 * time.Second
)

// newServer builds member name of a new cluster whose initial members' peer URLs are cluster and
// whose token is token: the member's peer URLs are peer, its one client URL http://client.
func newServer(name string, peer types.URLs, client string, cluster types.URLsMap, token string,
	lg *zap.Logger) (*etcdserver.EtcdServer, error) {
	cfg := config.ServerConfig{
		Name:    name,
		DataDir: name + ".etcd",
		// the initial members: a new cluster
		InitialPeerURLsMap:  cluster,
		PeerURLs:            peer,
		ClientURLs:          types.URLs{{Scheme: "http", Host: client}},
		InitialClusterToken: token,
		NewCluster:          true,
		// raft's clock (a positive tick: the raft node's ticker)
		TickMs:        100,
		ElectionTicks: 10,
		// etcd's default snapshot count; the catch-up entries past the theorems' step bound
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
		ServerFeatureGate: features.NewDefaultServerFeatureGate(name, lg),
	}
	return etcdserver.NewServer(cfg)
}

// StartServer starts the one member of a new cluster: member name, whose cluster token is its
// name, with the one peer URL http://peerAddr (not served: the cluster has no other member) and
// the one client URL http://clientAddr.
func StartServer(name string, peerAddr string, clientAddr string,
	lg *zap.Logger) (*etcdserver.EtcdServer, error) {
	peer := types.URLs{{Scheme: "http", Host: peerAddr}}
	s, err := newServer(name, peer, clientAddr, types.URLsMap{name: peer}, name, lg)
	if err != nil {
		return nil, err
	}
	s.Start()
	return s, nil
}

// NewMember builds member name of a new cluster whose initial members' peer URLs are cluster and
// whose token is token, its peer URLs peer (the one URL http://peerAddr) and its one client URL
// http://client, and serves its raft handler on a listener at peerAddr; it does not start it.
func NewMember(name string, peer types.URLs, peerAddr string, client string,
	cluster types.URLsMap, token string, lg *zap.Logger) (*etcdserver.EtcdServer, error) {
	s, err := newServer(name, peer, client, cluster, token, lg)
	if err != nil {
		return nil, err
	}
	// the member's peer URL is served by its own transport (D21b's deployment fact)
	l, err := net.Listen("tcp", peerAddr)
	if err != nil {
		return nil, err
	}
	go http.Serve(l, s.RaftHandler())
	return s, nil
}

// StartMember starts member name of a new cluster: NewMember, then the server started.
func StartMember(name string, peer types.URLs, peerAddr string, client string,
	cluster types.URLsMap, token string, lg *zap.Logger) (*etcdserver.EtcdServer, error) {
	s, err := NewMember(name, peer, peerAddr, client, cluster, token, lg)
	if err != nil {
		return nil, err
	}
	s.Start()
	return s, nil
}

// Serve serves the started member s's gRPC API (etcd's v3rpc.Server, no TLS, no extra
// interceptor) on a listener at addr, on a goroutine. The clients' keepalive pings are allowed
// every 5s, as etcd's embed does with its default GRPCKeepAliveMinTime (grpc's own default
// refuses a ping more often than every 5 minutes, which would close a keepalive client's
// connection).
func Serve(s *etcdserver.EtcdServer, addr string) error {
	gs := v3rpc.Server(s, nil, nil, grpc.KeepaliveEnforcementPolicy(keepalive.EnforcementPolicy{
		MinTime: 5 * time.Second,
	}))
	l, err := net.Listen("tcp", addr)
	if err != nil {
		return err
	}
	go gs.Serve(l)
	return nil
}

// NewClient connects a client to the one endpoint addr (a plain host:port, clientv3.New's premise
// plainEndpoint): NewClients of it.
func NewClient(addr string, lg *zap.Logger) (*clientv3.Client, error) {
	return NewClients([]string{addr}, lg)
}

// NewClients connects a client to the endpoints eps (plain host:ports), each call's attempt to one
// of them, configured as etcd's clients are in practice: the timeouts above (DialTimeout,
// keepalive) and etcd's default retries -- a read that fails with Unavailable is retried, on the
// next endpoint; a write is retried only after a refusal (a learner's, an authentication error),
// which the examples' members never send, so it is sent at most once (notes/read-retry-plan.md).
func NewClients(eps []string, lg *zap.Logger) (*clientv3.Client, error) {
	return clientv3.New(clientv3.Config{
		Endpoints:            eps,
		DialTimeout:          DialTimeout,
		DialKeepAliveTime:    KeepAliveTime,
		DialKeepAliveTimeout: KeepAliveTimeout,
		Logger:               lg,
	})
}
