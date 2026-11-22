// Package dist is k8s_safe's program (examples/k8s/all) as a distributed deployment, in the shape
// of etcd-dist's (examples/etcd/dist, notes/etcd-dist-plan.md stages D1 and D8): every etcd member a
// process of etcd-dist's server.Main on a machine of its own, and every Kubernetes component that is
// a client of etcd on a machine of its own, its checks on an orchestrator machine that reaches the
// components over Remote (examples/lib/remote). Two workloads, each on a cluster of its own as in
// k8s_all (the store's k1 members, the compactor's k2):
//
//   - store (store.go): the etcd3 store's workload (examples/k8s/etcd3's MainPartition): API server
//     machines, each Kubernetes' etcd3 storage over its own kubernetes client, and an orchestrator
//     that makes the clients' operations at them (remote.Do), records the history and checks it with
//     porcupine against the driver's model, then with Kubernetes' checker;
//   - compactor (compactor.go): Kubernetes' compactor (examples/k8s/compactor's MainPartition): a
//     writer machine, an API server machine per own compactor and one for the shared one, each API
//     server's loop one remote.Report whose log the orchestrator checks.
//
// The DaemonSet controller (examples/k8s/daemonset) is not here: it runs over the model API server
// (daemonset/apimodel), not over etcd. authz has no etcd either. Neither is in k8s_all's program.
//
// The programs are the drivers' code, called through copies of their packages (storecopy,
// compactorcopy: the drivers' unexported model, generator and checks), so that the drivers stay as
// k8s_safe's proof has them. dist_test.go deploys random deployments on machines of their own
// (network namespaces where available) and makes the faults (notes/k8s-dist.md).
package dist

import (
	"context"
	"net"
	"strconv"
	"sync"
	"time"

	clientv3 "go.etcd.io/etcd/client/v3"
	"go.uber.org/zap"

	"github.com/mit-pdos/etcd-grove/examples/etcd/dist/env"
	"github.com/mit-pdos/etcd-grove/examples/lib/etcdstart"
	"github.com/mit-pdos/etcd-grove/examples/lib/remote"
)

// Kind is a workload's kind.
type Kind int

const (
	Store Kind = iota
	Compactor
)

func (k Kind) String() string {
	if k == Store {
		return "store"
	}
	if k == Compactor {
		return "compactor"
	}
	return "unknown"
}

// Workload is a workload: for the store, Clients unary clients of Ops operations each and Watchers
// watchers of WOps watches each (the driver's clients, ops, watchers, wops), made at Apiservers API
// server machines (1 to Clients+Watchers); for the compactor, Rounds rounds of its API servers (the
// driver's is one).
type Workload struct {
	Kind       Kind
	Clients    int
	Ops        int
	Watchers   int
	WOps       int
	Apiservers int
	Rounds     int
}

// Result is how a workload's orchestrator ended: its check ran (a failed check is a panic), or why
// not; Why also says which checks ran.
type Result struct {
	Checked bool
	Why     string
}

func ended(why string) Result { return Result{Why: why} }

func (r Result) String() string {
	if r.Checked {
		return "checked (" + r.Why + ")"
	}
	return "ended without a check: " + r.Why
}

// Args is a process's configuration (a client machine's, as etcd-dist's client.Args): its
// workload, the members' client endpoints in the members' order, and the workload's addresses (the
// store's: client c's, len Clients+Watchers, on API server machine c mod Apiservers; the
// compactor's: its machine c's); on the orchestrator IsNode is false, on client machine Node it is
// true.
type Args struct {
	W      Workload
	Eps    []string
	Addrs  []string
	IsNode bool
	Node   int
}

// NodeCount is how many client machines a workload has.
func NodeCount(w Workload) int {
	if w.Kind == Store {
		return w.Apiservers
	}
	if w.Kind == Compactor {
		return CompactorMachines
	}
	return 0
}

// AddrCount is how many addresses a workload's client machines serve at.
func AddrCount(w Workload) int {
	if w.Kind == Store {
		return storeClients(w)
	}
	return NodeCount(w)
}

// How many times, and how far apart, awaitCluster tries its read and awaitNodes its connection
// (etcd-dist's).
const (
	readyTries = 60
	readyPause = 500 * time.Millisecond
	nodeTries  = 300
	nodePause  = 100 * time.Millisecond
)

// awaitCluster waits until a linearizable read through a client of eps returns (etcd-dist's: a
// liveness wait, a read writes nothing).
func awaitCluster(eps []string) bool {
	cli, err := etcdstart.NewClients(eps, zap.NewNop())
	if err != nil {
		return false
	}
	defer cli.Close()
	for t := 0; t < readyTries; t++ {
		ctx, cancel := context.WithTimeout(context.Background(), etcdstart.RequestTimeout)
		_, err := cli.Get(ctx, "dist/ready")
		cancel()
		if err == nil {
			return true
		}
		time.Sleep(readyPause)
	}
	return false
}

// awaitNodes waits until every address accepts a connection (etcd-dist's; a connection that
// carries no request runs nothing).
func awaitNodes(addrs []string) bool {
	for _, a := range addrs {
		up := false
		for t := 0; t < nodeTries && !up; t++ {
			c, err := net.DialTimeout("tcp", a, time.Second)
			if err == nil {
				c.Close()
				up = true
			} else {
				time.Sleep(nodePause)
			}
		}
		if !up {
			return false
		}
	}
	return true
}

// rotate is eps from its i-th (mod len) element on (etcd-dist's).
func rotate(eps []string, i int) []string {
	k := len(eps)
	out := make([]string, k)
	for j := 0; j < k; j++ {
		out[j] = eps[(i+j)%k]
	}
	return out
}

// connectRetry makes a clientv3 client of eps, trying until it succeeds.
func connectRetry(eps []string) *clientv3.Client {
	for {
		cli, err := etcdstart.NewClients(eps, zap.NewNop())
		if err == nil {
			return cli
		}
		time.Sleep(nodePause)
	}
}

// reportAll runs remote.Report at every address with its input, all at once (etcd-dist's).
func reportAll(addrs []string, ins []any, codec remote.Codec, d time.Duration) ([]any, []bool) {
	outs := make([]any, len(addrs))
	oks := make([]bool, len(addrs))
	var wg sync.WaitGroup
	for c := range addrs {
		wg.Add(1)
		go func() {
			outs[c], oks[c] = remote.Report(addrs[c], ins[c], codec, d)
			wg.Done()
		}()
	}
	wg.Wait()
	return outs, oks
}

// holdForever never returns.
func holdForever() {
	for {
		time.Sleep(time.Hour)
	}
}

func itoa(n int) string { return strconv.Itoa(n) }

// MainReady is workload w's orchestrator, against the members' client endpoints eps, its client
// machines at addrs: it clears the proxy variables, waits for the cluster's first read, and runs
// the workload. ready is called once its set-up is done (the store's seeds, every client machine
// answering), for the faults to start then; an observer only.
func MainReady(w Workload, eps []string, addrs []string, ready func()) Result {
	env.ClearProxy()
	if len(eps) == 0 {
		return ended("no endpoint")
	}
	if len(addrs) != AddrCount(w) {
		return ended("not one address per client")
	}
	if !awaitCluster(eps) {
		return ended("the cluster never answered a read")
	}
	switch w.Kind {
	case Store:
		if w.Apiservers < 1 || w.Apiservers > storeClients(w) {
			return ended("API server count")
		}
		return RunStore(w, eps, addrs, ready)
	case Compactor:
		return RunCompactor(w, addrs, ready)
	}
	return ended("unknown workload")
}

// NodeMain is workload w's client machine c: it clears the proxy variables and serves (store.go,
// compactor.go). It never returns but on a bad configuration.
func NodeMain(w Workload, c int, addrs []string, eps []string) {
	env.ClearProxy()
	if c < 0 || c >= NodeCount(w) || len(eps) == 0 || len(addrs) != AddrCount(w) {
		return
	}
	switch w.Kind {
	case Store:
		StoreNode(w, c, addrs, eps)
	case Compactor:
		CompactorNode(c, addrs[c], eps)
	}
}
