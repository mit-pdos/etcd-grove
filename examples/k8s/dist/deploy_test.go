package dist

// The test's side of the deployment (deploy.go): its description, and random well-formed
// deployments.

import (
	"fmt"
	"math/rand/v2"

	etcddist "github.com/mit-pdos/etcd-grove/examples/etcd/dist"
)

// String describes d for the logs.
func (d Deployment) String() string {
	w := d.StoreW
	return fmt.Sprintf("%v | store: clients %d x %d, watchers %d x %d, %d API servers | compactor: %d rounds",
		d.Cluster, w.Clients, w.Ops, w.Watchers, w.WOps, w.Apiservers, d.CompW.Rounds)
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

// RandomDeployment is a random well-formed deployment: the cluster of k members at addr(i), the
// store workload of sizes sz with watchers or not and a random API server count (one, every client
// its own, or between), the compactor's sz.Rounds rounds, each workload's client machines'
// addresses nodes(w).
func RandomDeployment(tag string, k int, addr func(int) (string, string), sz Sizes,
	nodes func(w Workload) []string) (Deployment, error) {
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
	d := Deployment{Cluster: cluster(tag, k, addr), StoreW: w, CompW: Workload{Kind: Compactor, Rounds: sz.Rounds}}
	d.StoreAddrs = nodes(d.StoreW)
	d.CompAddrs = nodes(d.CompW)
	return d, WellFormed(d)
}
