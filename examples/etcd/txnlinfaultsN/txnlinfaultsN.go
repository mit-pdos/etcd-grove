// Package txnlinfaultsN is examples/etcd/partition with any number of members
// (notes/txnlinfaultsN-plan.md): k etcd members started in-process with the examples' generic
// start (etcdstart.Members, etcdstart.StartMembers, as examples/etcd/putgetN starts them, here
// with partition's snapshot settings), each serving its raft handler on its own peer listener and
// etcd's gRPC API on its own client listener; a copy of etcd's test bridge (third_party/bridge) to
// each member's client address; k clients, each of every bridge (failover); a partitioner
// goroutine that cuts and mends the links between members (etcd's EtcdServer.CutPeer/MendPeer),
// and between each member and its clients (the bridge's Blackhole, Unblackhole and
// DropConnections), on a schedule Main is given (cluster3.Partitioner: its steps name members by
// index, below k); and partition's workload (partition.Check: lintest.Run with concurrent clients
// doing gets, ranges, puts, deletes and transactions, each through a client picked at random,
// checked by porcupine against txnlin's model). Main panics if porcupine finds the history not
// linearizable; the theorem (etcd_txnlinfaultsN_safe) is that it does not, for every schedule
// and every member count 1 <= k <= 1000.
//
// The workload and the partitioner are partition's and cluster3's, imported, so that their proofs
// carry over unchanged; only the start differs from partition's (cluster3.StartCluster, three
// members).
package txnlinfaultsN

import (
	"strconv"
	"time"

	"github.com/anishathalye/porcupine"
	"go.uber.org/zap"

	clientv3 "go.etcd.io/etcd/client/v3"
	"go.etcd.io/etcd/server/v3/etcdserver"

	"github.com/mit-pdos/etcd-grove/examples/etcd/partition"
	"github.com/mit-pdos/etcd-grove/examples/lib/cluster3"
	"github.com/mit-pdos/etcd-grove/examples/lib/etcdstart"
	"github.com/mit-pdos/etcd-grove/third_party/bridge"
)

// The members' address ranges: member i's peer address is 127.0.0.1:(PeerBase+i) (its one peer
// URL http://<addr>, served by its raft handler), its client address 127.0.0.1:(ClientBase+i)
// (served by its gRPC server), and its bridge's address 127.0.0.1:(BridgeBase+i) (the bridge to
// its client address, which the clients dial). Not another example's, so that the examples'
// tests can run at once.
const (
	PeerBase   uint64 = 26000
	ClientBase uint64 = 27000
	BridgeBase uint64 = 28000
)

// Token is the cluster's token (etcd's --initial-cluster-token), from which, with its peer URL,
// etcd computes each member's id (the SHA-1 of the peer URLs and the token, so member i's id is
// the same in every cluster of more than i members). The theorem's premise on the ids (their 16
// low bits distinct and not 0: etcd's request ids carry them as the member's prefix) fails for
// some k <= 1000 at most tokens (the birthday bound of 16 bits); this token is the first
// "txnlinfaultsN-<i>" at which it holds for every k <= 1000 (TestMemberIDs checks it), as
// putgetN's, and at which it holds also across the clusters of examples/etcd/all (etcd_safe's
// Hlow: this cluster at k <= 1000, the other k-member ones at k <= 300; its TestMemberIDs).
const Token = "txnlinfaultsN-12748"

// The members' snapshot settings (partition's): a disk snapshot every SnapCount applied entries,
// raft's log then compacted to SnapCatchUp entries below it, so that a member a cut kept behind
// is caught up, once mended, by a snapshot (MsgSnap) rather than by entries.
const (
	SnapCount   uint64 = 1
	SnapCatchUp uint64 = 1
)

// bridgeAddr is member i's bridge address, 127.0.0.1:(BridgeBase+i), the number in decimal (as
// etcdstart.Members writes the members' addresses).
func bridgeAddr(i uint64) string {
	return "127.0.0.1:" + strconv.FormatUint(BridgeBase+i, 10)
}

// holdToken sleeps forever (cluster3's): Main runs it on a goroutine of its own beside each
// member's gRPC server, which touches no lock; the proof hands that goroutine's thread token to
// the member's serving (etcdstart.Serve's GoAttach resources), as cluster3.StartMember does.
func holdToken() {
	for {
		time.Sleep(time.Hour)
	}
}

// startCluster starts the k members of a new cluster (etcdstart.Members, etcdstart.StartMembers),
// then, for each member in order, its gRPC server on its client address (etcdstart.Serve, with a
// holdToken goroutine beside it) and a bridge to that address (cluster3.StartBridge), and then k
// clients, each of every bridge (etcdstart.NewClients: failover). It returns the members, the
// bridges and the clients, and false if a step failed (the specs allow every step to fail).
func startCluster(k uint64, lg *zap.Logger) ([]*etcdserver.EtcdServer, []bridge.Bridge,
	[]*clientv3.Client, bool) {
	ms := etcdstart.Members("txnlinfaultsN", k, PeerBase, ClientBase)
	srvs, err := etcdstart.StartMembers(ms, Token, SnapCount, SnapCatchUp, lg)
	if err != nil {
		return nil, nil, nil, false
	}
	brs := make([]bridge.Bridge, k)
	baddrs := make([]string, k)
	for i := uint64(0); i < k; i++ {
		go holdToken()
		if err := etcdstart.Serve(srvs[i], ms[i].Client); err != nil {
			return nil, nil, nil, false
		}
		ba := bridgeAddr(i)
		br, err := cluster3.StartBridge(ba, ms[i].Client)
		if err != nil {
			return nil, nil, nil, false
		}
		brs[i] = br
		baddrs[i] = ba
	}
	clis := make([]*clientv3.Client, k)
	for j := uint64(0); j < k; j++ {
		cli, err := etcdstart.NewClients(baddrs, lg)
		if err != nil {
			return nil, nil, nil, false
		}
		clis[j] = cli
	}
	return srvs, brs, clis, true
}

// Main starts the k-member cluster (startCluster), starts the partitioner on sched and runs
// partition's Check of clients concurrent clients of ops operations each; it panics if porcupine
// finds the history illegal. A failed start, or k = 0, ends Main without a check.
func Main(k uint64, clients int, ops int, sched []cluster3.Step) porcupine.CheckResult {
	if k == 0 {
		return porcupine.Unknown
	}
	srvs, brs, clis, ok := startCluster(k, zap.NewNop())
	if !ok {
		return porcupine.Unknown
	}
	go cluster3.Partitioner(srvs, brs, sched)
	r := partition.Check(clis, clients, ops, 0)
	if r == porcupine.Illegal {
		panic("txnlinfaultsN: porcupine found the history not linearizable")
	}
	return r
}
