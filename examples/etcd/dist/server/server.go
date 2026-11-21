//go:build etcddist_sketch

// Package server is the program of an etcd member machine of etcd_dist_safe
// (notes/etcd-dist-plan.md; DRAFT, a sketch: not built, not translated, kept out of every build by
// its build tag). One process runs one member: Main builds the member from its configuration
// (etcdstart's newServerMode, with the server configuration a parameter), serves its raft handler
// on its peer address and etcd's gRPC API on its client address, starts it, and runs until the
// machine crashes. The same Main is the machine's boot program after a crash: etcd's NewServer
// finds the member's WAL in its data directory and restarts the member from it (bootstrap's
// haveWAL path); the initial cluster's map and token are then ignored by etcd.
//
// Written against the models' limits (etcd-grove#24, lean 715d5e6753): plain TCP listeners
// (net.Listen at an address the net extension's addrOk accepts), http.Server.Serve and
// grpc.Server.Serve on the program's own listeners, insecure credentials, no compression, no
// TLS. Two known gaps, marked TODO(model): v3rpc.Server installs otelgrpc.NewServerHandler, a
// stats handler the grpc model does not take yet (phase 7 S1); and rafthttp's client side
// (pipeline, stream, snapshot: http.Transport.RoundTrip, chunked bodies) is phase 7 S5.
package server

import (
	"net"
	"net/http"
	"os"
	"time"

	"go.uber.org/zap"
	"google.golang.org/grpc"
	"google.golang.org/grpc/keepalive"

	"go.etcd.io/etcd/client/pkg/v3/types"
	"go.etcd.io/etcd/server/v3/config"
	"go.etcd.io/etcd/server/v3/etcdserver"
	"go.etcd.io/etcd/server/v3/etcdserver/api/v3rpc"
	"go.etcd.io/etcd/server/v3/features"

	"github.com/mit-pdos/etcd-grove/examples/lib/etcdstart"
)

// Peer is one initial member of the cluster: its name and its peer address (its one peer URL is
// http://Addr).
type Peer struct {
	Name string
	Addr string
}

// Config is a member's configuration: the deployment's (Lean: Deployment, Cluster, ServerCfg)
// as one member sees it.
type Config struct {
	Name    string // this member's name (its data directory DataBase/<Name>.etcd)
	Peer    string // its peer address, served by its raft handler
	Client  string // its client address, served by its gRPC API
	Cluster []Peer // the initial cluster, this member included
	Token   string // the cluster's token (etcd's --initial-cluster-token)
	// the server configuration (Lean: ServerCfg; the same at every member)
	CompactorMode string // "", "revision" or "periodic" ("" when Retention is 0)
	Retention     int64  // revisions, or nanoseconds; 0: the auto-compactor off
	SnapCount     uint64
	CatchUp       uint64
	Auth          bool // the simple token provider (TTL 300 s), or none
}

// clearProxyEnv makes the deployment proxy-free: Go's http.ProxyFromEnvironment (rafthttp's
// transports) reads these once, at its first use, which is after this. With non-loopback
// addresses this is what lets the theorem do without a proxy premise (etcd-grove#24). It also
// clears ETCD_VERIFY, so that verifyEnvOff becomes a fact of the program rather than a premise.
// TODO(model): needs specs of os.Unsetenv and of the environment as machine-local state.
func clearProxyEnv() {
	os.Unsetenv("HTTP_PROXY")
	os.Unsetenv("HTTPS_PROXY")
	os.Unsetenv("NO_PROXY")
	os.Unsetenv("http_proxy")
	os.Unsetenv("https_proxy")
	os.Unsetenv("no_proxy")
	os.Unsetenv("ETCD_VERIFY")
}

// holdForever keeps the process alive: a member runs until its machine crashes.
func holdForever() {
	for {
		time.Sleep(time.Hour)
	}
}

// Main runs one member (see the package doc). An error from a step ends Main (and the process)
// without a panic: the theorem then has nothing to say about this member's later behavior, and
// its peers see it as a member that never answers.
func Main(c Config) {
	clearProxyEnv()
	lg := zap.NewNop()
	cluster := types.URLsMap{}
	for _, p := range c.Cluster {
		cluster[p.Name] = types.URLs{{Scheme: "http", Host: p.Addr}}
	}
	cfg := config.ServerConfig{
		Name:                    c.Name,
		DataDir:                 etcdstart.DataBase + "/" + c.Name + ".etcd",
		DedicatedWALDir:         etcdstart.WALBase + "/" + c.Name + ".etcd" + "/wal",
		InitialPeerURLsMap:      cluster,
		PeerURLs:                cluster[c.Name],
		ClientURLs:              types.URLs{{Scheme: "http", Host: c.Client}},
		InitialClusterToken:     c.Token,
		NewCluster:              true,
		TickMs:                  100,
		ElectionTicks:           10,
		SnapshotCount:           c.SnapCount,
		SnapshotCatchUpEntries:  c.CatchUp,
		MaxTxnOps:               128,
		MaxRequestBytes:         1536 * 1024,
		AutoCompactionMode:      c.CompactorMode,
		AutoCompactionRetention: time.Duration(c.Retention),
		Logger:                  lg,
		ServerFeatureGate:       features.NewDefaultServerFeatureGate(c.Name, lg),
	}
	if c.Auth {
		cfg.AuthToken = "simple"
		cfg.TokenTTL = 300
	}
	s, err := etcdserver.NewServer(cfg) // a first start, or a restart from the WAL
	if err != nil {
		return
	}
	pl, err := net.Listen("tcp", c.Peer)
	if err != nil {
		return
	}
	// the raft handler only (as the examples' members): /leases is a 404 on every peer
	// (leasePeersOk holds by construction of the deployment). Open question Q8.
	go (&http.Server{Handler: s.RaftHandler()}).Serve(pl)
	s.Start()
	// TODO(model): v3rpc.Server installs otelgrpc.NewServerHandler (phase 7 S1).
	gs := v3rpc.Server(s, nil, nil, grpc.KeepaliveEnforcementPolicy(keepalive.EnforcementPolicy{
		MinTime: 5 * time.Second,
	}))
	cl, err := net.Listen("tcp", c.Client)
	if err != nil {
		return
	}
	go gs.Serve(cl)
	holdForever()
}
