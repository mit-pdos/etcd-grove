// Package restart3 is putget3 (examples/putget3) with a member stopped and started again on its
// data directory (notes/restart-plan.md): three etcd members started in-process, a Put through the
// first, a follower other than the first stopped (HardStop, its peer listener closed), more Puts
// through the first, that member started again -- same name, data directory and addresses -- and a
// Get through it, checked against the last Put. Only the first member's gRPC API is served before
// the restart, and the restarted member's after it. The members take a snapshot every other entry
// and keep one entry below it (linkv3p's settings), so the restarted member finds a snapshot in its
// WAL and is caught up by a snapshot from the leader.
//
// Main panics if the check fails; the adequacy theorem to prove is that it does not. An error from
// any step ends Main without a check, as in putget3.
package restart3

import (
	"context"
	"net"
	"net/http"

	"go.uber.org/zap"

	"go.etcd.io/etcd/client/pkg/v3/types"
	clientv3 "go.etcd.io/etcd/client/v3"
	"go.etcd.io/etcd/server/v3/etcdserver"

	"github.com/mit-pdos/etcd-grove/examples/common"
)

// The members' peer and client addresses (each member's one peer URL is http://<peer addr>, its
// raft handler's; its client address is its gRPC server's, a plain host:port). Not another
// example's, so that the examples' tests can run at once.
const (
	peerAddr1   = "127.0.0.1:23861"
	peerAddr2   = "127.0.0.1:23862"
	peerAddr3   = "127.0.0.1:23863"
	clientAddr1 = "127.0.0.1:23864"
	clientAddr2 = "127.0.0.1:23865"
	clientAddr3 = "127.0.0.1:23866"
)

// The members' snapshot settings (common.BuildServer): a disk snapshot every SnapCount applied
// entries, raft's log then compacted to SnapCatchUp entries below it, so that the stopped member
// is caught up by a snapshot once started again.
const (
	SnapCount   uint64 = 1
	SnapCatchUp uint64 = 1
)

// NPuts is the number of Puts made while the third member is stopped: enough that the leader
// compacts its log past the stopped member's last index.
const NPuts = 20

// A member: its server and its peer listener (serving its raft handler), kept so that stop can
// close it.
type member struct {
	s  *etcdserver.EtcdServer
	pl net.Listener
}

// startMember starts member name of the cluster cluster (token "restart3"), whose peer URLs are
// peer (the one URL http://peerAddr): the server built (common.BuildServer, at the snapshot
// settings), its raft handler served on a listener at peerAddr, and the server started. Its client
// URL is http://client, served only by serveClient. Starting a member that was stopped finds its
// data directory (the member's name + ".etcd"): etcd restarts it from its WAL.
func startMember(name string, peer types.URLs, peerAddr string, client string,
	cluster types.URLsMap, lg *zap.Logger) (*member, error) {
	s, err := common.BuildServer(name, peer, client, cluster, "restart3", SnapCount, SnapCatchUp, lg)
	if err != nil {
		return nil, err
	}
	pl, err := net.Listen("tcp", peerAddr)
	if err != nil {
		return nil, err
	}
	go http.Serve(pl, s.RaftHandler())
	s.Start()
	return &member{s: s, pl: pl}, nil
}

// serveClient serves the started member m's gRPC API on a listener at client (common.Serve). An
// address is served once in a run: member 1's from the start, the restarted member's only after
// its restart (the proofs' network model binds an address's gRPC server for good).
func serveClient(m *member, client string) error {
	return common.Serve(m.s, client)
}

// stop stops the member m: the server stopped (HardStop: no leadership transfer; run's deferred
// shutdown stops the raft node and the transport and calls Cleanup, which closes the lessor, the KV
// store, the auth store and the backend, so that the data directory can be opened again; Cleanup
// must not be called again: a second lessor.Stop closes a closed channel), then its peer listener
// closed, so that the restarted member can listen on the address again.
func stop(m *member) {
	m.s.HardStop()
	m.pl.Close()
}

// put puts key k with value v through cli, in a context with the request timeout, cancelled after
// the call.
func put(cli *clientv3.Client, k string, v string) error {
	ctx, cancel := context.WithTimeout(context.Background(), common.RequestTimeout)
	_, err := cli.Put(ctx, k, v)
	cancel()
	return err
}

// Run is Main with the logger lg (the members' and the clients'), so that a test can count what
// the members log.
func Run(lg *zap.Logger) {
	peer1 := types.URLs{{Scheme: "http", Host: peerAddr1}}
	peer2 := types.URLs{{Scheme: "http", Host: peerAddr2}}
	peer3 := types.URLs{{Scheme: "http", Host: peerAddr3}}
	cluster := types.URLsMap{"restart3-1": peer1, "restart3-2": peer2, "restart3-3": peer3}

	m1, err := startMember("restart3-1", peer1, peerAddr1, clientAddr1, cluster, lg)
	if err != nil {
		return
	}
	m2, err := startMember("restart3-2", peer2, peerAddr2, clientAddr2, cluster, lg)
	if err != nil {
		return
	}
	m3, err := startMember("restart3-3", peer3, peerAddr3, clientAddr3, cluster, lg)
	if err != nil {
		return
	}

	if err := serveClient(m1, clientAddr1); err != nil {
		return
	}
	cli, err := common.NewClient(clientAddr1, lg)
	if err != nil {
		return
	}
	if err := put(cli, "k", "v1"); err != nil {
		return
	}

	// a follower stopped (Q6 of the plan: no election forced): member 3, or member 2 if member 3
	// leads (the client's member 1 is never stopped); the others keep the quorum
	name, peer, peerAddr, client, m := "restart3-3", peer3, peerAddr3, clientAddr3, m3
	if m3.s.Leader() == m3.s.MemberID() {
		name, peer, peerAddr, client, m = "restart3-2", peer2, peerAddr2, clientAddr2, m2
	}
	stop(m)
	for i := 0; i < NPuts; i++ {
		if err := put(cli, "k", "v2"); err != nil {
			return
		}
	}

	// the stopped member started again on its data directory
	mR, err := startMember(name, peer, peerAddr, client, cluster, lg)
	if err != nil {
		return
	}
	if err := serveClient(mR, client); err != nil {
		return
	}
	cliR, err := common.NewClient(client, lg)
	if err != nil {
		return
	}
	gctx, gcancel := context.WithTimeout(context.Background(), common.RequestTimeout)
	resp, err := cliR.Get(gctx, "k")
	gcancel()
	if err != nil {
		return
	}
	if len(resp.Kvs) == 0 || string(resp.Kvs[0].Value) != "v2" {
		panic("restart3: the restarted member's Get did not return the last Put's value")
	}
}

// Main runs the example with no logging (Run).
func Main() {
	Run(zap.NewNop())
}
