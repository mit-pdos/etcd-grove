package dist

// The deployment: one etcd cluster, an etcd-dist deployment of members with no etcd workload (its
// members run etcd-dist's server.MainDeployment), which both workloads use at once, as one etcd
// cluster serves all of a Kubernetes control plane's API servers, its compaction running while they
// serve (k8s_all's program has two clusters: notes/k8s-dist.md, "One cluster"); the workloads'
// sizes; and the workloads' client machines' addresses. WellFormed is etcd-dist's predicate on the
// cluster, with what the k8s drivers fix of their clusters: etcd's own compactor off (every
// compaction is a Kubernetes compactor's) and no auth (the drivers' clients log in as nobody).
//
// The machines' programs, as etcd-dist's (client.Orchestrator, client.NodeDeployment): the
// orchestrator of workload j (0: the store, 1: the compactor) is Orchestrator(d, j), the n-th
// client machine NodeDeployment(d, n) (the store's API server machines, then the compactor's),
// each checking d first.

import (
	"fmt"

	"github.com/mit-pdos/etcd-grove/examples/etcd/dist/deployment"
)

// Deployment is a k8s deployment: the cluster, the two workloads over it, and their client
// machines' addresses: StoreAddrs the store's clients' (AddrCount(StoreW), client c's served by
// API server machine c mod StoreW.Apiservers), CompAddrs the compactor's machines'
// (CompactorMachines).
type Deployment struct {
	Cluster    deployment.Deployment
	StoreW     Workload
	CompW      Workload
	StoreAddrs []string
	CompAddrs  []string
}

// The workloads' indices (Orchestrator's j).
const (
	StoreWorkload     = 0
	CompactorWorkload = 1
)

// Workload is d's workload j and its addresses; ok is false if d has no workload j.
func (d Deployment) Workload(j int) (w Workload, addrs []string, ok bool) {
	if j == StoreWorkload {
		return d.StoreW, d.StoreAddrs, true
	}
	if j == CompactorWorkload {
		return d.CompW, d.CompAddrs, true
	}
	return Workload{}, nil, false
}

// Node is the n-th client machine of d (the store's API server machines, then the compactor's):
// its workload's index j and its index c among the workload's client machines; ok is false if d
// has no n-th client machine.
func (d Deployment) Node(n int) (j int, c int, ok bool) {
	if n < 0 {
		return 0, 0, false
	}
	s := NodeCount(d.StoreW)
	if n < s {
		return StoreWorkload, n, true
	}
	n -= s
	if n < NodeCount(d.CompW) {
		return CompactorWorkload, n, true
	}
	return 0, 0, false
}

// WellFormed checks d: the cluster etcd-dist's WellFormed with no auth, no etcd compactor and no
// etcd workload; the store workload's bounds (the driver's clients+watchers < 2^31, every count
// non-negative, at least one client, 1 to clients+watchers API servers); the compactor's at least
// one round; every client machine address valid (deployment.AddrOk), of at most deployment.MaxLen
// bytes, distinct from each other and from the members', AddrCount of them per workload.
func WellFormed(d Deployment) error {
	c := d.Cluster
	if err := deployment.WellFormed(c); err != nil {
		return err
	}
	if c.Cfg.Auth || c.Cfg.Retention != 0 || len(c.Workloads) != 0 {
		return fmt.Errorf("the cluster has auth, etcd's compactor or an etcd workload")
	}
	w := d.StoreW
	n := w.Clients + w.Watchers
	if w.Kind != Store || w.Clients < 0 || w.Watchers < 0 || w.Ops < 0 || w.WOps < 0 || n < 1 ||
		n >= 1<<31 || w.Apiservers < 1 || w.Apiservers > n {
		return fmt.Errorf("store workload bounds")
	}
	if d.CompW.Kind != Compactor || d.CompW.Rounds < 1 {
		return fmt.Errorf("compactor workload")
	}
	if len(d.StoreAddrs) != AddrCount(d.StoreW) || len(d.CompAddrs) != AddrCount(d.CompW) {
		return fmt.Errorf("client machine address counts")
	}
	seen := map[string]bool{}
	for _, m := range c.Members {
		seen[m.Peer] = true
		seen[m.Client] = true
	}
	for _, as := range [][]string{d.StoreAddrs, d.CompAddrs} {
		for _, a := range as {
			if len(a) > deployment.MaxLen || !deployment.AddrOk(a) || seen[a] {
				return fmt.Errorf("client machine address %q", a)
			}
			seen[a] = true
		}
	}
	return nil
}

// MainDeployment is workload j's orchestrator machine of the deployment d: if d is well formed and
// has a workload j, MainReady of that workload, the members' client endpoints and the workload's
// addresses; otherwise it returns at once. ready is MainReady's (an observer only).
func MainDeployment(d Deployment, j int, ready func()) Result {
	if WellFormed(d) != nil {
		return ended("the deployment is not well formed")
	}
	w, addrs, ok := d.Workload(j)
	if !ok {
		return ended("no such workload")
	}
	return MainReady(w, d.Cluster.Endpoints(), addrs, ready)
}

// Orchestrator is workload j's orchestrator machine of the deployment d, as a statement over the
// deployment names it: MainDeployment with no set-up signal (the test's signal, a file marker, is
// the harness's), its result discarded (a failed check panics).
func Orchestrator(d Deployment, j int) {
	MainDeployment(d, j, func() {})
}

// NodeDeployment is the n-th client machine of the deployment d (Deployment.Node): if d is well
// formed and has an n-th client machine, NodeMain, client machine c of workload j over the
// workload's addresses; otherwise it returns at once.
func NodeDeployment(d Deployment, n int) {
	if WellFormed(d) != nil {
		return
	}
	j, c, ok := d.Node(n)
	if !ok {
		return
	}
	w, addrs, _ := d.Workload(j)
	NodeMain(w, c, addrs, d.Cluster.Endpoints())
}
