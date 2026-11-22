// Package server is the program of an etcd member machine of etcd_dist_safe
// (notes/etcd-dist-plan.md, §2). One process runs one member: Main builds the member from its
// configuration (etcdstart's newServerMode, with the server configuration a parameter), serves
// etcd's peer handler on its peer address, starts it, waits until it is ready, serves etcd's gRPC
// API on its client address, and runs until the machine crashes. The same Main is the machine's
// boot program after a crash: etcd's NewServer finds the member's WAL in its WAL area and restarts
// the member from it (bootstrap's haveWAL path); the initial cluster's map and token are then
// ignored by etcd.
//
// Written against the models' limits (etcd-grove#24; the plan's §2, U1-U3): plain TCP listeners at
// the configuration's addresses verbatim (net.Listen at an address the net extension's addrOk
// accepts, the same string in the member's URLs and in the clients' endpoints), http.Server.Serve
// and grpc.Server.Serve on the program's own listeners (no cmux), insecure gRPC, no compression, no
// TLS. Two known gaps: v3rpc.Server installs otelgrpc.NewServerHandler, a stats handler the grpc
// model takes only from phase 7 S1 (U2); and rafthttp's client side (pipeline, stream, snapshot:
// http.Transport.RoundTrip, chunked bodies) is phase 7 S5.
//
// Nothing here is a copy of a driver's code: etcdstart's newServerMode is unexported and fixes the
// snapshot and token-provider settings, so the configuration is built here (the same fields, the
// examples' fixed values for the others: plan Q9); etcdstart.Serve is not used because it serves
// on a goroutine before returning, where Main serves only after ReadyNotify (review F4), which
// etcdstart.Serve's callers do not need.
package server

import (
	"net"
	"net/http"
	"time"

	"go.uber.org/zap"
	"google.golang.org/grpc"
	"google.golang.org/grpc/keepalive"

	"go.etcd.io/etcd/client/pkg/v3/types"
	"go.etcd.io/etcd/server/v3/config"
	"go.etcd.io/etcd/server/v3/etcdserver"
	"go.etcd.io/etcd/server/v3/etcdserver/api/etcdhttp"
	"go.etcd.io/etcd/server/v3/etcdserver/api/v3rpc"
	"go.etcd.io/etcd/server/v3/features"

	"github.com/mit-pdos/etcd-grove/examples/etcd/dist/env"
	"github.com/mit-pdos/etcd-grove/examples/lib/etcdstart"
)

// Peer is one initial member of the cluster: its name and its peer address (its one peer URL is
// http://Addr).
type Peer struct {
	Name string
	Addr string
}

// The auto-compactor's modes (etcd's --auto-compaction-mode, v3compactor.ModeRevision and
// ModePeriodic).
const (
	CompactorRevision = "revision"
	CompactorPeriodic = "periodic"
)

// Config is a member's configuration: the deployment's (Lean: Deployment, Member, ServerCfg) as
// one member sees it. Its data directory is etcdstart.DataBase/<Name>.etcd and its WAL area
// etcdstart.WALBase/<Name>.etcd (the WAL in its wal subdirectory), as every example's member.
type Config struct {
	Name    string // this member's name (Lean: nameOk)
	Peer    string // its peer address, served by etcd's peer handler; its entry in Cluster
	Client  string // its client address, served by etcd's gRPC API, verbatim the clients' endpoint
	Cluster []Peer // the initial cluster, this member included
	Token   string // the cluster's token (etcd's --initial-cluster-token)
	// The server configuration (Lean: ServerCfg; the same at every member).
	CompactorMode string // CompactorRevision or CompactorPeriodic (ignored when Retention is 0)
	Retention     int64  // revisions (revision mode) or nanoseconds (periodic); 0: no auto-compactor
	SnapCount     uint64 // a disk snapshot every SnapCount applied entries (etcd's --snapshot-count)
	CatchUp       uint64 // raft's log kept CatchUp entries below a snapshot
	Auth          bool   // the simple token provider (TTL 300 s), or none
}

// holdForever keeps the process alive: a member runs until its machine crashes.
func holdForever() {
	for {
		time.Sleep(time.Hour)
	}
}

// serverConfig is the member's etcd configuration: c's, with the examples' fixed values for the
// rest (etcdstart's newServerMode and StartMemberAuth).
func serverConfig(c Config, lg *zap.Logger) config.ServerConfig {
	cluster := types.URLsMap{}
	for _, p := range c.Cluster {
		cluster[p.Name] = types.URLs{{Scheme: "http", Host: p.Addr}}
	}
	mode := c.CompactorMode
	if c.Retention == 0 {
		mode = ""
	}
	cfg := config.ServerConfig{
		Name:                    c.Name,
		DataDir:                 etcdstart.DataBase + "/" + c.Name + ".etcd",
		DedicatedWALDir:         etcdstart.WALBase + "/" + c.Name + ".etcd" + "/wal",
		InitialPeerURLsMap:      cluster,
		PeerURLs:                types.URLs{{Scheme: "http", Host: c.Peer}},
		ClientURLs:              types.URLs{{Scheme: "http", Host: c.Client}},
		InitialClusterToken:     c.Token,
		NewCluster:              true,
		TickMs:                  100,
		ElectionTicks:           10,
		SnapshotCount:           c.SnapCount,
		SnapshotCatchUpEntries:  c.CatchUp,
		MaxTxnOps:               128,
		MaxRequestBytes:         1536 * 1024,
		AutoCompactionMode:      mode,
		AutoCompactionRetention: time.Duration(c.Retention),
		Logger:                  lg,
		ServerFeatureGate:       features.NewDefaultServerFeatureGate(c.Name, lg),
	}
	if c.Auth {
		cfg.AuthToken = "simple"
		cfg.TokenTTL = 300
	}
	return cfg
}

// inCluster says whether c's own name and peer address are an entry of its initial cluster.
func inCluster(c Config) bool {
	for _, p := range c.Cluster {
		if p.Name == c.Name && p.Addr == c.Peer {
			return true
		}
	}
	return false
}

// Main runs one member with no logging (MainLogger).
func Main(c Config) {
	MainLogger(c, zap.NewNop())
}

// MainLogger runs one member (see the package doc), logging to lg. An error from a step ends it
// (and the process) without a panic: the theorem then has nothing to say about this member's
// later behavior, and its peers see it as a member that never answers.
func MainLogger(c Config, lg *zap.Logger) {
	env.ClearProxy()
	if !inCluster(c) {
		return
	}
	// a first start, or a restart from the WAL
	s, err := etcdserver.NewServer(serverConfig(c, lg))
	if err != nil {
		return
	}
	pl, err := net.Listen("tcp", c.Peer)
	if err != nil {
		return
	}
	// etcd's full peer handler (plan Q8), as embed serves it: raft, /members, /members/promote,
	// /leases and /leases/internal (a follower's TimeToLive and KeepAlive forwarded to the leader),
	// the hash and downgrade paths, /version.
	go (&http.Server{Handler: etcdhttp.NewPeerHandler(lg, s)}).Serve(pl)
	s.Start()
	// Clients are served only once the member is ready (review F4): after a crash the backend may lag
	// the WAL until the replay re-applies what the power loss took from bbolt; ReadyNotify closes once
	// the member's own publish entry is applied, after every entry committed before the crash (etcd's
	// embed waits the same way before serving clients). TODO(proof): whether the server's specs can
	// give ReadyNotify this meaning (plan D6).
	<-s.ReadyNotify()
	// insecure gRPC (no TLS: nil), no extra interceptor; the clients' keepalive pings allowed every
	// 5 s, as etcdstart.Serve (and embed's default GRPCKeepAliveMinTime). TODO(model): v3rpc.Server
	// installs otelgrpc.NewServerHandler (phase 7 S1).
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
