// Package cluster3 starts a three-member etcd cluster in-process under network partitions, for the
// examples that run a workload on one (examples/etcd/partition, examples/k8s/compactorp): each
// member started as examples/etcd/putget3 starts it (etcdstart.NewMember), serving its raft handler
// on its own peer listener and etcd's gRPC API on its own client listener; a bridge to each
// member's client address (third_party/bridge, the TCP proxy of etcd's integration tests'
// ClusterConfig.UseBridge), which the clients dial; and a partitioner that cuts and mends the links
// between members, and between each member and its clients, on a schedule.
//
// The partitions are etcd's own: EtcdServer.CutPeer and MendPeer, which etcd's integration tests
// use (tests/framework/integration/cluster.go, InjectPartition/RecoverPartition), pause and
// resume the transport's peer, which then drops every message to and from it. Both directions of
// a link are cut and mended together, as those tests do. The cuts between the clients and a member
// are the bridge's: Blackhole drops every byte both ways until Unblackhole closes the proxied
// connections, and DropConnections closes them. A client recovers by itself: its calls wait for a
// connection (clientv3's default WaitForReady), and gRPC re-dials the bridge.
//
// Until 2026-11-05 this was package partition's own (examples/etcd/partition); it moved here when
// a second example needed it (notes/k8s-compactor-plan.md, K6).
package cluster3

import (
	"net"
	"time"

	"go.uber.org/zap"
	"google.golang.org/grpc"
	"google.golang.org/grpc/keepalive"

	"go.etcd.io/etcd/client/pkg/v3/types"
	clientv3 "go.etcd.io/etcd/client/v3"
	"go.etcd.io/etcd/server/v3/etcdserver"
	"go.etcd.io/etcd/server/v3/etcdserver/api/v3rpc"

	"github.com/mit-pdos/etcd-grove/examples/lib/etcdstart"
	"github.com/mit-pdos/etcd-grove/third_party/bridge"
)

// Config is a cluster's: its token, its members' names, peer addresses (each member's one peer URL
// is http://<addr>, served by that member's raft handler), client addresses (each served by the
// member's gRPC server) and bridge addresses (each the bridge to a member's client address, which
// the clients dial: a plain host:port, clientv3.New's premise), and the members' snapshot settings
// (etcdstart.NewMember).
type Config struct {
	Token       string
	Name1       string
	Name2       string
	Name3       string
	Peer1       string
	Peer2       string
	Peer3       string
	Client1     string
	Client2     string
	Client3     string
	Bridge1     string
	Bridge2     string
	Bridge3     string
	SnapCount   uint64
	SnapCatchUp uint64
}

// The kinds of a schedule's step.
const (
	// cut the link between members A and B, both directions (CutPeer)
	PeerCut = 0
	// mend it (MendPeer)
	PeerMend = 1
	// cut member A's clients off it: every byte between them dropped (the bridge's Blackhole)
	ClientBlackhole = 2
	// end that: the bridge's connections closed, new ones forwarded (Unblackhole)
	ClientUnblackhole = 3
	// close the connections between member A and its clients (the bridge's DropConnections)
	ClientDrop = 4
)

// A Step of a partition schedule: after Delay, its Kind's action on members A and B (indices into
// the cluster's members, 0 to 2): a peer step cuts or mends the link between A and B in both
// directions; a client step acts on the link between member A and its clients (B unused). A step
// whose indices are out of range (or equal, for a peer step), or whose kind is none of the above,
// does nothing.
type Step struct {
	Delay time.Duration
	Kind  int
	A     int
	B     int
}

// StartMember starts member name of the new cluster cluster, whose peer URLs are peer (the one
// URL http://peerAddr): the server and its raft handler served on a listener at peerAddr (the
// examples' shared NewMember, with the cluster's token and snapshot settings), the server started,
// and its gRPC server served on a listener at client.
func StartMember(name string, peer types.URLs, peerAddr string, client string,
	cluster types.URLsMap, token string, snapCount uint64, catchUp uint64,
	lg *zap.Logger) (*etcdserver.EtcdServer, error) {
	// the server (configured as putget3's) and its raft handler
	s, err := etcdstart.NewMember(name, peer, peerAddr, client, cluster, token, snapCount, catchUp,
		lg)
	if err != nil {
		return nil, err
	}
	// the member's client address, before the server starts (an error leaves nothing running)
	cl, err := net.Listen("tcp", client)
	if err != nil {
		return nil, err
	}
	s.Start()
	// the clients' keepalive pings allowed every 5s, as etcd's embed does with its default
	// GRPCKeepAliveMinTime (grpc's own default refuses a ping more often than every 5 minutes)
	gs := v3rpc.Server(s, nil, nil, grpc.KeepaliveEnforcementPolicy(keepalive.EnforcementPolicy{
		MinTime: 5 * time.Second,
	}))
	go gs.Serve(cl)
	return s, nil
}

// StartBridge starts a bridge at addr to the member's client address client: the listener, then
// the bridge's accept loop (bridge.New).
func StartBridge(addr string, client string) (bridge.Bridge, error) {
	l, err := net.Listen("tcp", addr)
	if err != nil {
		return nil, err
	}
	return bridge.New(client, l), nil
}

// PeerStep applies a peer step to the members srvs: cuts or mends the link between members a and
// b in both directions (etcd's CutPeer/MendPeer, as its integration tests'
// InjectPartition/RecoverPartition).
func PeerStep(srvs []*etcdserver.EtcdServer, kind int, a int, b int) {
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

// ClientStep applies a client step to member a's bridge (brs[a]), as etcd's integration tests
// do (Member.Bridge().Blackhole(), ...); holed[a] says whether that bridge is blackholed. A
// blackhole of a blackholed bridge does nothing: the bridge's Blackhole closes its channel
// unguarded, so a second one would panic (issues/nonissues/etcd-bridge-blackhole-twice-panic.md).
func ClientStep(brs []bridge.Bridge, holed []bool, kind int, a int) {
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

// Partitioner applies the schedule sched to the members srvs and their bridges brs: each step,
// after its delay.
func Partitioner(srvs []*etcdserver.EtcdServer, brs []bridge.Bridge, sched []Step) {
	holed := make([]bool, len(brs))
	for _, st := range sched {
		time.Sleep(st.Delay)
		if st.Kind == PeerCut || st.Kind == PeerMend {
			PeerStep(srvs, st.Kind, st.A, st.B)
		} else if st.Kind == ClientBlackhole || st.Kind == ClientUnblackhole || st.Kind == ClientDrop {
			ClientStep(brs, holed, st.Kind, st.A)
		}
	}
}

// StartCluster starts the three members of a new cluster of configuration cfg and a bridge to
// each member's client address. It returns the members and the bridges, and false if a step
// failed (the specs allow every step to fail).
func StartCluster(cfg Config, lg *zap.Logger) ([]*etcdserver.EtcdServer, []bridge.Bridge, bool) {
	peer1 := types.URLs{{Scheme: "http", Host: cfg.Peer1}}
	peer2 := types.URLs{{Scheme: "http", Host: cfg.Peer2}}
	peer3 := types.URLs{{Scheme: "http", Host: cfg.Peer3}}
	cluster := types.URLsMap{cfg.Name1: peer1, cfg.Name2: peer2, cfg.Name3: peer3}

	s1, err := StartMember(cfg.Name1, peer1, cfg.Peer1, cfg.Client1, cluster, cfg.Token,
		cfg.SnapCount, cfg.SnapCatchUp, lg)
	if err != nil {
		return nil, nil, false
	}
	s2, err := StartMember(cfg.Name2, peer2, cfg.Peer2, cfg.Client2, cluster, cfg.Token,
		cfg.SnapCount, cfg.SnapCatchUp, lg)
	if err != nil {
		return nil, nil, false
	}
	s3, err := StartMember(cfg.Name3, peer3, cfg.Peer3, cfg.Client3, cluster, cfg.Token,
		cfg.SnapCount, cfg.SnapCatchUp, lg)
	if err != nil {
		return nil, nil, false
	}
	srvs := []*etcdserver.EtcdServer{s1, s2, s3}

	br1, err := StartBridge(cfg.Bridge1, cfg.Client1)
	if err != nil {
		return nil, nil, false
	}
	br2, err := StartBridge(cfg.Bridge2, cfg.Client2)
	if err != nil {
		return nil, nil, false
	}
	br3, err := StartBridge(cfg.Bridge3, cfg.Client3)
	if err != nil {
		return nil, nil, false
	}
	brs := []bridge.Bridge{br1, br2, br3}
	return srvs, brs, true
}

// NewClient connects a client to the cluster of configuration cfg through every member's bridge:
// an attempt goes to one of them (failover); the examples' client configuration
// (etcdstart.NewClients: etcdctl's timeouts and keepalive, the default retries -- a write is sent
// at most once, these members sending no refusal, notes/read-retry-plan.md; keepalive closes a
// connection that stops answering, notes/keepalive-plan.md).
func NewClient(cfg Config, lg *zap.Logger) (*clientv3.Client, error) {
	return etcdstart.NewClients([]string{cfg.Bridge1, cfg.Bridge2, cfg.Bridge3}, lg)
}
