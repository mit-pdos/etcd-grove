// Package leasecatchup is the lease example of a three-member cluster whose member catches up by a
// snapshot (notes/lease-mono3-plan.md, lease-mono3 step 1): three etcd members started in-process
// as examples/etcd/partition starts them (examples/lib/cluster3), snapshots taken often and raft's
// log compacted right below them (SnapCount, SnapCatchUp); a lease granted through member 3; member
// 3 then cut off the two others, filler leases granted through member 1 until the leader's log is
// compacted past member 3's, and the links mended, so that the leader catches member 3 up by a
// snapshot, which member 3 installs (applySnapshot, its lessor recovered from the snapshot's lease
// bucket). Main panics if member 3, once it lists the last filler (it has caught up), does not list
// the lease granted through it; the theorem to prove is that it does not, under the deployment
// premise that no lease granted in the run expires before the run ends (the TTL is an hour; the run
// takes seconds).
//
// Each client is of one member (etcdstart.NewClients of that member's bridge), not of the cluster:
// a member's listing reads only its own lessor (LeaseLeases), and a grant's spec is per member.
//
// Main calls only what the proofs specify: cluster3's StartCluster and PeerStep, etcdstart's
// NewClients, the clients' Grant and Leases (through their Lease field), each in a context with
// the examples' request timeout (context.WithTimeout of Background, cancelled after the call), and
// time.Sleep. An error from a step of the start or from the first grant ends Main without a check;
// a filler's error is ignored; a listing that fails, or that does not yet list the last filler, is
// retried a bounded number of times, after which Main ends without a check.
package leasecatchup

import (
	"context"
	"time"

	"go.uber.org/zap"

	clientv3 "go.etcd.io/etcd/client/v3"

	"github.com/mit-pdos/etcd-grove/examples/lib/cluster3"
	"github.com/mit-pdos/etcd-grove/examples/lib/etcdstart"
)

// The members' peer, client and bridge addresses: not another example's, so that the examples'
// tests can run at once.
const (
	peerAddr1   = "127.0.0.1:24011"
	peerAddr2   = "127.0.0.1:24012"
	peerAddr3   = "127.0.0.1:24013"
	clientAddr1 = "127.0.0.1:24021"
	clientAddr2 = "127.0.0.1:24022"
	clientAddr3 = "127.0.0.1:24023"
	bridgeAddr1 = "127.0.0.1:24031"
	bridgeAddr2 = "127.0.0.1:24032"
	bridgeAddr3 = "127.0.0.1:24033"
)

// The members' snapshot settings (etcdstart.NewMember), examples/etcd/partition's: a disk snapshot
// every SnapCount applied entries, raft's log then compacted to SnapCatchUp entries below it, so
// that a member a cut kept behind is caught up, once mended, by a snapshot.
const (
	SnapCount   uint64 = 1
	SnapCatchUp uint64 = 1
)

// The TTL every lease is granted with, in seconds: far longer than the run.
const grantTTL = 3600

// The number of filler grants made while member 3 is cut off (see the test for why it suffices).
const fillers = 20

// The number of listings of member 3's leases tried after the mend, and the pause after each one
// that does not list the last filler.
const (
	polls     = 60
	pollDelay = 250 * time.Millisecond
)

// run's results: the check passed; a step of the start, or the first grant, failed; member 3 never
// listed the last filler (or no filler was granted).
const (
	Checked     = 0
	StartFailed = 1
	NotCaughtUp = 2
)

// config is the cluster's (cluster3.Config): its token, member names and addresses, and snapshot
// settings.
func config() cluster3.Config {
	return cluster3.Config{
		Token: "leasecatchup", Name1: "leasecatchup-1", Name2: "leasecatchup-2",
		Name3: "leasecatchup-3",
		Peer1: peerAddr1, Peer2: peerAddr2, Peer3: peerAddr3,
		Client1: clientAddr1, Client2: clientAddr2, Client3: clientAddr3,
		Bridge1: bridgeAddr1, Bridge2: bridgeAddr2, Bridge3: bridgeAddr3,
		SnapCount: SnapCount, SnapCatchUp: SnapCatchUp,
	}
}

// grant grants a lease of TTL grantTTL through cli, in a context with the request timeout.
func grant(cli *clientv3.Client) (*clientv3.LeaseGrantResponse, error) {
	ctx, cancel := context.WithTimeout(context.Background(), etcdstart.RequestTimeout)
	g, err := cli.Lease.Grant(ctx, grantTTL)
	cancel()
	return g, err
}

// leases lists the leases of cli's member, in a context with the request timeout.
func leases(cli *clientv3.Client) (*clientv3.LeaseLeasesResponse, error) {
	ctx, cancel := context.WithTimeout(context.Background(), etcdstart.RequestTimeout)
	ls, err := cli.Lease.Leases(ctx)
	cancel()
	return ls, err
}

// listed says whether the listing ls has the lease id.
func listed(ls *clientv3.LeaseLeasesResponse, id clientv3.LeaseID) bool {
	found := false
	for i := range ls.Leases {
		if ls.Leases[i].ID == id {
			found = true
		}
	}
	return found
}

// run is Main with the members' logger lg: it starts the cluster, grants a lease through member 3,
// cuts member 3 off, grants the fillers through member 1, mends the links, waits for member 3 to
// list the last filler and checks that it lists the first lease too.
func run(lg *zap.Logger) int {
	cfg := config()
	srvs, _, ok := cluster3.StartCluster(cfg, lg)
	if !ok {
		return StartFailed
	}
	c3, err := etcdstart.NewClients([]string{cfg.Bridge3}, lg)
	if err != nil {
		return StartFailed
	}
	c1, err := etcdstart.NewClients([]string{cfg.Bridge1}, lg)
	if err != nil {
		return StartFailed
	}

	// 1. the lease granted through member 3 (which applied it before answering)
	g1, err := grant(c3)
	if err != nil {
		return StartFailed
	}

	// 2. member 3 cut off the two others
	cluster3.PeerStep(srvs, cluster3.PeerCut, 2, 0)
	cluster3.PeerStep(srvs, cluster3.PeerCut, 2, 1)

	// 3. the fillers, through member 1: the log grows, the leader snapshots and compacts it
	var last clientv3.LeaseID
	granted := false
	for i := 0; i < fillers; i++ {
		f, err := grant(c1)
		if err == nil {
			last = f.ID
			granted = true
		}
	}
	if !granted {
		return NotCaughtUp
	}

	// 4. the links mended
	cluster3.PeerStep(srvs, cluster3.PeerMend, 2, 0)
	cluster3.PeerStep(srvs, cluster3.PeerMend, 2, 1)

	// 5. member 3's listing, until it has the last filler; 6. then it must have g1
	for p := 0; p < polls; p++ {
		ls, err := leases(c3)
		if err == nil && listed(ls, last) {
			if !listed(ls, g1.ID) {
				panic("leasecatchup: member 3 caught up and lost the lease granted through it")
			}
			return Checked
		}
		time.Sleep(pollDelay)
	}
	return NotCaughtUp
}

// Main runs the example (run) with no logging.
func Main() {
	run(zap.NewNop())
}
