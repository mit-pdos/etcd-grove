package dist

// The store workload: examples/k8s/etcd3's MainPartition with its API servers on machines of their
// own. The driver runs Kubernetes' etcd3 store in one process with its clients; here the store
// runs on API server machines (StoreNode), each its own Kubernetes etcd3 storage over a
// kubernetes client of its own to the cluster, as API servers of an HA control plane do, and the
// orchestrator (RunStore) issues the clients' operations to them over Remote (remote.Do), records
// the history and checks it: porcupine against the driver's Model, then, on a failure-free history,
// Kubernetes' own checker (realCheck), as the driver's Check does. Client c's operations are made
// by API server c mod A (A API server machines), each client at its own address on that machine
// (one remote.Serve each), so that an API server serves several clients at once, as the driver's
// one store serves all of them.

import (
	"sync/atomic"
	"time"

	"github.com/anishathalye/porcupine"
	"go.uber.org/zap"

	clientv3 "go.etcd.io/etcd/client/v3"
	"go.etcd.io/etcd/client/v3/kubernetes"

	"github.com/mit-pdos/etcd-grove/examples/lib/etcdstart"
	"github.com/mit-pdos/etcd-grove/examples/lib/lintest"
	"github.com/mit-pdos/etcd-grove/examples/lib/remote"

	k8s "github.com/mit-pdos/etcd-grove/examples/k8s/dist/storecopy"
)

// StoreAttempt is how long one attempt of a store call may take: a unary call has no deadline of
// its own in the driver (it ends when keepalive closes a dead transport, etcdstart's KeepAliveTime
// and KeepAliveTimeout), and a watch takes about watchDuration and its hiccups. A call that takes
// longer is a call without an answer: a write's outcome unknown, a read's tried again.
const StoreAttempt = 30 * time.Second

// CheckTimeout bounds each porcupine check (the driver's and Kubernetes' model): a check that
// times out is Unknown, an end without a verdict, never a failure.
const CheckTimeout = 5 * time.Minute

// storeClients are the store workload's clients: its unary clients, then its watchers.
func storeClients(w Workload) int {
	return w.Clients + w.Watchers
}

// newKubeClient connects a kubernetes client to eps as the driver's startCluster does
// (etcdstart's timeouts and keepalive, the default retries), trying until it succeeds.
func newKubeClient(eps []string) *kubernetes.Client {
	for {
		kc, err := kubernetes.New(clientv3.Config{
			Endpoints:            eps,
			DialTimeout:          etcdstart.DialTimeout,
			DialKeepAliveTime:    etcdstart.KeepAliveTime,
			DialKeepAliveTimeout: etcdstart.KeepAliveTimeout,
			Logger:               zap.NewNop(),
		})
		if err == nil {
			return kc
		}
		time.Sleep(nodePause)
	}
}

// StoreNode is API server machine a of the store workload w: its store (the driver's, without the
// seeds: storecopy.NewStoreOnly) over a kubernetes client of eps from member a on, then, for every
// client c with c mod A = a, remote.Serve at addrs[c] whose operation is the driver's call (or
// runWatch) through that store. It never returns.
func StoreNode(w Workload, a int, addrs []string, eps []string) {
	kc := newKubeClient(rotate(eps, a))
	s, ok := k8s.NewStoreOnly(kc)
	if !ok {
		panic("k8sdist: the API server's store could not be made")
	}
	op := func(sys any, in any) any {
		return k8s.Serve(s, in.(k8s.Input))
	}
	for c := 0; c < storeClients(w); c++ {
		if c%w.Apiservers == a {
			go remote.Serve(addrs[c], s, op, StoreCodec(), StoreAttempt)
		}
	}
	holdForever()
}

// RunStore is the store workload's orchestrator: it seeds the keys through a client of eps (the
// driver's seed: revisions 2 and 3 of the fresh cluster), waits for its API server machines, calls
// ready, then runs the driver's Check with the operations made at the API servers (remote.Do at
// addrs[c] for client c), the per-client cache kept here (storecopy.Record, Apply's bookkeeping).
// It panics if porcupine finds the history not linearizable against the driver's Model, or if
// Kubernetes' checker rejects a failure-free one, as the driver does.
func RunStore(w Workload, eps []string, addrs []string, ready func()) Result {
	if !k8s.SetFeatures() {
		return ended("the features could not be set")
	}
	cli, err := etcdstart.NewClients(eps, zap.NewNop())
	if err != nil {
		return ended("no client")
	}
	seeded, ok := k8s.Seed(cli)
	cli.Close()
	if !ok {
		return ended("the seeds failed or did not make revisions 2 and 3")
	}
	if !awaitNodes(addrs) {
		return ended("an API server machine never answered")
	}
	ready()
	tbl := seeded.NewCache(w.Clients, w.Ops)
	var rawLost atomic.Bool
	codec := StoreCodec()
	apply := func(input any) any {
		in := input.(k8s.Input)
		so := remote.Do(addrs[in.Client], in, codec, StoreAttempt).(StoreOut)
		k8s.Record(tbl, in, so.Out)
		if !so.RawOK {
			rawLost.Store(true)
		}
		return so.Out
	}
	gen := func(id int) any { return k8s.Gen(tbl, id) }
	r, lops := lintest.RunLin2(seeded.Model(), apply, gen, lintest.CounterClock(), w.Clients, w.Ops,
		w.Watchers, w.WOps, CheckTimeout)
	if r == porcupine.Illegal {
		panic("k8sdist: porcupine found the store's history not linearizable")
	}
	if r != porcupine.Ok {
		return ended("porcupine timed out")
	}
	if !k8s.FailureFree(lops) {
		return Result{Checked: true, Why: "model only: a call failed"}
	}
	if rawLost.Load() {
		return Result{Checked: true, Why: "model only: a raw answer did not cross the wire"}
	}
	rr := seeded.RealCheck(lops, CheckTimeout)
	if rr == porcupine.Illegal {
		panic("k8sdist: Kubernetes' checker rejected the store's history")
	}
	if rr != porcupine.Ok {
		return Result{Checked: true, Why: "model only: Kubernetes' checker timed out"}
	}
	return Result{Checked: true, Why: "model and Kubernetes' checker"}
}
