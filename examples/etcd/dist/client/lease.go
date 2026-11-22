package client

import (
	"context"
	"time"

	clientv3 "go.etcd.io/etcd/client/v3"

	"github.com/mit-pdos/etcd-grove/examples/lib/etcdstart"
)

// The lease workloads: none writes a key (Lean: writesKeys false), so they run beside the
// workloads that read revisions as their own. Their checks read one member's lessor, so each of
// their clients is of one member (eps[i]), not of the cluster.

// The id leaseRead's TimeToLive asks about (leaseN's: any id; the workloads beside it grant leases
// with ids of the members' prefixes, never 7).
const leaseReadID = clientv3.LeaseID(7)

// leaseExpiry's TTL (below the members' minimum: the lessor grants the minimum, 2 s at the
// members' 10 ticks of 100 ms), and how often and how many times a listing is polled (leaseexpiryN's).
const (
	expiryTTL   = 1
	expiryPolls = 80
	expiryEvery = 250 * time.Millisecond
)

// leaseCatchup's fillers, and how many times, how far apart, its member's listing is polled
// (leasecatchup's; more polls, since a member may be down for a while).
const (
	catchupFillers = 20
	catchupPolls   = 120
	catchupEvery   = 250 * time.Millisecond
)

// leaseGrant grants a lease of TTL ttl through cli, in a context with the request timeout
// (leasecatchup's and leaseexpiryN's grant, copied, with the TTL a parameter).
func leaseGrant(cli *clientv3.Client, ttl int64) (*clientv3.LeaseGrantResponse, error) {
	ctx, cancel := context.WithTimeout(context.Background(), etcdstart.RequestTimeout)
	g, err := cli.Lease.Grant(ctx, ttl)
	cancel()
	return g, err
}

// leaseList lists the leases of cli's member, in a context with the request timeout (the lease
// drivers' leases, copied).
func leaseList(cli *clientv3.Client) (*clientv3.LeaseLeasesResponse, error) {
	ctx, cancel := context.WithTimeout(context.Background(), etcdstart.RequestTimeout)
	ls, err := cli.Lease.Leases(ctx)
	cancel()
	return ls, err
}

// listed says whether the listing ls has the lease id (the lease drivers', copied).
func listed(ls *clientv3.LeaseLeasesResponse, id clientv3.LeaseID) bool {
	found := false
	for i := range ls.Leases {
		if ls.Leases[i].ID == id {
			found = true
		}
	}
	return found
}

// leaseReadCheck (leaseN's check, copied) makes the two reads through a new client of the member
// at addr and panics if either answers wrongly: Leases lists no id twice, TimeToLive answers about
// the lease asked. It reports whether both answered.
func leaseReadCheck(addr string) bool {
	cli, err := newClient([]string{addr})
	if err != nil {
		return false
	}
	defer cli.Close()
	ls, err := leaseList(cli)
	if err != nil {
		return false
	}
	for i := range ls.Leases {
		for j := 0; j < i; j++ {
			if ls.Leases[i].ID == ls.Leases[j].ID {
				panic("dist leaseRead: Leases listed a lease twice")
			}
		}
	}
	tctx, tcancel := context.WithTimeout(context.Background(), etcdstart.RequestTimeout)
	ttl, err := cli.Lease.TimeToLive(tctx, leaseReadID)
	tcancel()
	if err != nil {
		return false
	}
	if ttl.ID != leaseReadID {
		panic("dist leaseRead: TimeToLive answered about another lease")
	}
	return true
}

// RunLeaseRead is the leaseRead workload (leaseN's run minus its members' gRPC serving; Lean:
// Workload.leaseRead): leaseReadCheck at every member in turn. Unlike leaseN's, a member whose
// reads fail does not end the workload: the others are still checked.
func RunLeaseRead(eps []string) Result {
	n := 0
	for _, a := range eps {
		if leaseReadCheck(a) {
			n++
		}
	}
	if n == 0 {
		return ended("leaseRead: no member's reads answered")
	}
	return checked()
}

// RunLeaseCatchup is the leaseCatchup workload (leasecatchup's run minus its start and its cut,
// copied; Lean: Workload.leaseCatchup): a lease of etcd's MaxLeaseTTL (no lease of the workload
// expires: Workload.needsNoExpiry) granted through the last member; fillers granted through the
// first; then the last member's listing polled until it lists the last filler that was granted,
// and then it must list the first lease too. leasecatchup cuts the last member off while the
// fillers are granted so that it catches up by a snapshot; here any cut, and any catch-up, is the
// network's and the crashes' (a run that takes the snapshot path is one execution among those
// the theorem covers; plan §6).
func RunLeaseCatchup(eps []string, ready func()) Result {
	k := len(eps)
	c3, err := newClient([]string{eps[k-1]})
	if err != nil {
		return ended("leaseCatchup: a client failed to connect")
	}
	defer c3.Close()
	c1, err := newClient([]string{eps[0]})
	if err != nil {
		return ended("leaseCatchup: a client failed to connect")
	}
	defer c1.Close()
	g1, err := leaseGrant(c3, maxLeaseTTL)
	if err != nil {
		return ended("leaseCatchup: the first grant failed")
	}
	ready()
	var last clientv3.LeaseID
	granted := false
	for i := 0; i < catchupFillers; i++ {
		f, err := leaseGrant(c1, maxLeaseTTL)
		if err == nil {
			last = f.ID
			granted = true
		}
	}
	if !granted {
		return ended("leaseCatchup: no filler was granted")
	}
	for p := 0; p < catchupPolls; p++ {
		ls, err := leaseList(c3)
		if err == nil && listed(ls, last) {
			if !listed(ls, g1.ID) {
				panic("dist leaseCatchup: the member caught up and lost the lease granted through it")
			}
			return checked()
		}
		time.Sleep(catchupEvery)
	}
	return ended("leaseCatchup: the member never listed the last filler")
}

// gone (leaseexpiryN's, copied) polls cli's member's listing until it does not list id, and
// reports whether it saw that within the polls. Unlike leaseexpiryN's, a listing's error does not
// end the polling (the member may be down a while).
func gone(cli *clientv3.Client, id clientv3.LeaseID) bool {
	for i := 0; i < expiryPolls; i++ {
		time.Sleep(expiryEvery)
		ls, err := leaseList(cli)
		if err == nil && !listed(ls, id) {
			return true
		}
	}
	return false
}

// RunLeaseExpiry is the leaseExpiry workload (leaseexpiryN's run minus its members' gRPC serving,
// copied; Lean: Workload.leaseExpiry): a lease of the shortest TTL granted through each member;
// then, member by member, its listing polled until it no longer lists the lease granted through
// it, then listed once more: panics if that listing has the lease again. A member whose grant
// failed is skipped (its lease may exist: an unknown outcome, which the check never looks at).
func RunLeaseExpiry(eps []string) Result {
	clis := make([]*clientv3.Client, len(eps))
	ids := make([]clientv3.LeaseID, len(eps))
	ok := make([]bool, len(eps))
	for j, a := range eps {
		cli, err := newClient([]string{a})
		if err != nil {
			return ended("leaseExpiry: a client failed to connect")
		}
		defer cli.Close()
		clis[j] = cli
		g, err := leaseGrant(cli, expiryTTL)
		if err == nil {
			ids[j] = g.ID
			ok[j] = true
		}
	}
	n := 0
	for j := range eps {
		if !ok[j] || !gone(clis[j], ids[j]) {
			continue
		}
		ls, err := leaseList(clis[j])
		if err != nil {
			continue
		}
		if listed(ls, ids[j]) {
			panic("dist leaseExpiry: a member listed an expired lease again")
		}
		n++
	}
	if n == 0 {
		return ended("leaseExpiry: no member's check ran")
	}
	return checked()
}
