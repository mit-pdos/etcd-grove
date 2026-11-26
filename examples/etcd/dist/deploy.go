// Package dist runs etcd_safe's deployments for real (notes/etcd-dist-plan.md, stage D1)
// over examples/lib/robust: every member a process of server.Main on a
// machine of its own, every workload a process of client.Main on a client machine of its own, all
// started at once and connected by TCP through examples/lib/robust's network; meanwhile the environment
// makes the faults the theorem's executions allow: members crash for real (SIGKILL, then their
// files synced, or their disk losing power where the device mapper is available) and restart with
// the same program and configuration, and the network partitions (both ways or one way) and
// delays, loses, duplicates and reorders packets (robust.NetNemesis, in the namespace mode). The
// programs have no fault of their own.
//
// A run passes if no process panics (a client's failed check, or a member's panic) and no member
// exits on its own, and every client is done by the deadline. A client that ends without a check
// (its start failed, a watch ended, a lease was never seen gone) is not a failure: the theorem
// says nothing more; the test reports how many checks ran.
//
// Every machine receives the whole deployment and its own index (examples/etcd/dist/deployment;
// server.MainDeployment, client.MainDeployment, client.NodeDeployment), and checks it first
// (deployment.WellFormed, the Lean predicate's Go mirror). The deployments are random among the
// well-formed ones of a fixed member count: a random server configuration and a random compatible
// mix of workloads.
package dist

import (
	"fmt"
	"math/rand/v2"
	"time"

	"github.com/mit-pdos/etcd-grove/examples/etcd/dist/deployment"
)

// The deployment's types and its check, from package deployment (the machines' programs import it).
type (
	Deployment = deployment.Deployment
	Member     = deployment.Member
	ServerCfg  = deployment.ServerCfg
	Workload   = deployment.Workload
)

// WellFormed is deployment.WellFormed.
func WellFormed(d Deployment) error { return deployment.WellFormed(d) }

// Sizes are the workloads' sizes in a random deployment.
type Sizes struct {
	KVClients, KVOps   int
	Writers, WriterOps int
	DurablePuts        int
}

// ShortSizes and FullSizes are the short mode's and the full test's.
var (
	ShortSizes = Sizes{KVClients: 3, KVOps: 25, Writers: 3, WriterOps: 15, DurablePuts: 40}
	FullSizes  = Sizes{KVClients: 4, KVOps: 200, Writers: 4, WriterOps: 200, DurablePuts: 256}
)

// pick is a random element of xs.
func pick[T any](xs ...T) T { return xs[rand.IntN(len(xs))] }

// RandomWorkloads is a random compatible mix of workloads of the sizes sz: one workload that reads revisions as its own (kv,
// watch or cache) or some of compact, putget and durable, each perhaps with leaseRead; or auth or
// authLease alone; or lease workloads alone (leaseRead, and leaseCatchup or leaseExpiry: a workload
// that grants leases runs beside no key writer, and leaseExpiry never beside leaseCatchup).
func RandomWorkloads(sz Sizes) []Workload {
	var ws []Workload
	switch rand.IntN(9) {
	case 0, 1:
		ws = append(ws, Workload{Kind: deployment.KV, Clients: sz.KVClients, Ops: sz.KVOps})
	case 2:
		ws = append(ws, Workload{Kind: deployment.Watch, Clients: sz.Writers, Ops: sz.WriterOps})
	case 3:
		ws = append(ws, Workload{Kind: deployment.Cache, Clients: sz.Writers, Ops: sz.WriterOps})
	case 4, 5:
		for len(ws) == 0 {
			if rand.IntN(2) == 0 {
				ws = append(ws, Workload{Kind: deployment.Compact})
			}
			if rand.IntN(2) == 0 {
				ws = append(ws, Workload{Kind: deployment.PutGet})
			}
			if rand.IntN(2) == 0 {
				ws = append(ws, Workload{Kind: deployment.Durable, Clients: sz.DurablePuts})
			}
		}
	case 6:
		return []Workload{{Kind: deployment.Auth}}
	case 7:
		return []Workload{{Kind: deployment.AuthLease}}
	case 8:
		for len(ws) == 0 {
			if rand.IntN(2) == 0 {
				ws = append(ws, Workload{Kind: deployment.LeaseRead})
			}
			switch rand.IntN(3) {
			case 0:
				ws = append(ws, Workload{Kind: deployment.LeaseCatchup})
			case 1:
				ws = append(ws, Workload{Kind: deployment.LeaseExpiry})
			}
		}
		return ws
	}
	if rand.IntN(2) == 0 {
		ws = append(ws, Workload{Kind: deployment.LeaseRead})
	}
	return ws
}

// randomCfg is a random supported server configuration for the workloads ws: the token provider
// exactly if a workload needs it; the compactor off,
// in revision mode or in periodic mode (not beside compact); snapshots often or rarely.
func randomCfg(ws []Workload) ServerCfg {
	var c ServerCfg
	auth, compact := false, false
	for _, w := range ws {
		auth = auth || deployment.NeedsAuth(w.Kind)
		compact = compact || w.Kind == deployment.Compact
	}
	c.Auth = auth
	switch rand.IntN(4) {
	case 1:
		c.CompactorMode, c.Retention = deployment.CompactorRevision, pick[int64](1, 10, 1000)
	case 2:
		if !compact {
			c.CompactorMode, c.Retention = deployment.CompactorPeriodic, pick(int64(10*time.Millisecond), int64(time.Second))
		}
	}
	c.SnapCount = pick[uint64](1, 10, 100, 10000)
	c.CatchUp = pick[uint64](1, 5, 100, 1<<48)
	return c
}

// RandomDeployment is a random well-formed deployment of k members at the addresses addr(i)
// (peer and client), its names and token tagged by tag, with the workloads ws (RandomWorkloads)
// and their client machines' addresses nodes (nodes[j]: deployment.NodeCount(ws[j]) of them): a
// random server configuration for ws, and the first token tag-<n> whose member ids pass
// WellFormed's condition 3.
func RandomDeployment(tag string, k int, addr func(i int) (peer, client string), ws []Workload, nodes [][]string) (Deployment, error) {
	d := Deployment{Cfg: randomCfg(ws), Workloads: ws, Nodes: nodes}
	for i := 0; i < k; i++ {
		p, c := addr(i)
		d.Members = append(d.Members, Member{Name: fmt.Sprintf("%s-%d", tag, i), Peer: p, Client: c})
	}
	for n := 0; n < 1000; n++ {
		d.Token = fmt.Sprintf("%s-%d", tag, n)
		if deployment.IdsOk(d) {
			break
		}
	}
	return d, WellFormed(d)
}
