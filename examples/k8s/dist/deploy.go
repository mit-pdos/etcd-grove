package dist

// The deployment: two etcd clusters, as k8s_all's two (the store's and the compactor's), each an
// etcd-dist deployment of members with no etcd workload (its members run etcd-dist's server.Main),
// and the store workload's sizes. WellFormed is etcd-dist's predicate on each cluster, with what
// the k8s drivers fix of their clusters: etcd's own compactor off (the store's driver has no
// compactor, the compactor's makes every compaction a client's) and no auth (the drivers' clients
// log in as nobody).

import (
	"fmt"
	"math/rand/v2"

	etcddist "github.com/mit-pdos/etcd-grove/examples/etcd/dist/harness"
)

// Deployment is a k8s deployment: the store's cluster with its workload, the compactor's cluster
// (its workload has no sizes).
type Deployment struct {
	Store     etcddist.Deployment
	StoreW    Workload
	Compactor etcddist.Deployment
	CompW     Workload
}

func (d Deployment) String() string {
	w := d.StoreW
	return fmt.Sprintf("store: %v; clients %d x %d, watchers %d x %d, %d API servers | compactor: %v; %d rounds",
		d.Store, w.Clients, w.Ops, w.Watchers, w.WOps, w.Apiservers, d.Compactor, d.CompW.Rounds)
}

// WellFormed checks d: each cluster etcd-dist's WellFormed with no auth and no etcd compactor; the
// two clusters' member names and addresses disjoint; the store workload's bounds (the driver's
// clients+watchers < 2^31, every count non-negative, at least one client, 1 to clients+watchers
// API servers).
func WellFormed(d Deployment) error {
	for _, c := range []etcddist.Deployment{d.Store, d.Compactor} {
		if err := etcddist.WellFormed(c); err != nil {
			return err
		}
		if c.Cfg.Auth || c.Cfg.Retention != 0 || len(c.Workloads) != 0 {
			return fmt.Errorf("a k8s cluster has auth, etcd's compactor or an etcd workload")
		}
	}
	seen := map[string]bool{}
	for _, c := range []etcddist.Deployment{d.Store, d.Compactor} {
		for _, m := range c.Members {
			for _, s := range []string{"name " + m.Name, m.Peer, m.Client} {
				if seen[s] {
					return fmt.Errorf("%s in both clusters", s)
				}
				seen[s] = true
			}
		}
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
	return nil
}

// Sizes are the store workload's sizes in a random deployment: the clients' and watchers' counts
// and operations, and the compactor's rounds.
type Sizes struct {
	Clients, Ops, Watchers, WOps int
	Rounds                       int
}

// ShortSizes and FullSizes are the short mode's and the full test's (the driver's tests use 4
// clients of 60 operations).
var (
	ShortSizes = Sizes{Clients: 3, Ops: 30, Watchers: 1, WOps: 5, Rounds: 2}
	FullSizes  = Sizes{Clients: 4, Ops: 200, Watchers: 2, WOps: 20, Rounds: 20}
)

// cluster is a random cluster of k members at addr(i), named and its token tagged by tag: a random
// snapshot setting (etcd-dist's choices), no auth, no compactor; the first token tag-<n> whose ids
// pass etcd-dist's WellFormed.
func cluster(tag string, k int, addr func(i int) (peer, client string)) etcddist.Deployment {
	snap := []uint64{1, 10, 100, 10000}
	catch := []uint64{1, 5, 100, 1 << 48}
	d := etcddist.Deployment{Cfg: etcddist.ServerCfg{SnapCount: snap[rand.IntN(len(snap))],
		CatchUp: catch[rand.IntN(len(catch))]}}
	for i := 0; i < k; i++ {
		p, c := addr(i)
		d.Members = append(d.Members, etcddist.Member{Name: fmt.Sprintf("%s-%d", tag, i), Peer: p, Client: c})
	}
	for n := 0; n < 1000; n++ {
		d.Token = fmt.Sprintf("%s-%d", tag, n)
		if etcddist.WellFormed(d) == nil {
			break
		}
	}
	return d
}

// RandomDeployment is a random well-formed deployment: the store's cluster of k1 members at
// addr1(i), the compactor's of k2 at addr2(i), the store workload of sizes sz with watchers or not
// and a random API server count (one, every client its own, or between).
func RandomDeployment(tag string, k1 int, addr1 func(int) (string, string), k2 int,
	addr2 func(int) (string, string), sz Sizes) (Deployment, error) {
	w := Workload{Kind: Store, Clients: sz.Clients, Ops: sz.Ops}
	if rand.IntN(3) != 0 {
		w.Watchers, w.WOps = sz.Watchers, sz.WOps
	}
	n := w.Clients + w.Watchers
	switch rand.IntN(3) {
	case 0:
		w.Apiservers = 1
	case 1:
		w.Apiservers = n
	default:
		w.Apiservers = 1 + rand.IntN(n)
	}
	d := Deployment{Store: cluster(tag+"s", k1, addr1), StoreW: w, Compactor: cluster(tag+"c", k2, addr2),
		CompW: Workload{Kind: Compactor, Rounds: sz.Rounds}}
	return d, WellFormed(d)
}
