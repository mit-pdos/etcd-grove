package dist

// The store workload: examples/k8s/etcd3's MainPartition with its API servers on machines of their
// own. The driver runs Kubernetes' etcd3 store in one process with its clients; here the store
// runs on API server machines (StoreNode), each its own Kubernetes etcd3 storage over a
// kubernetes client of its own to the cluster, as API servers of an HA control plane do, and the
// orchestrator (RunStore) issues the clients' operations to them over Remote (remote.Do), records
// the history and checks it: porcupine against the driver's Model with foreign revisions (the
// cluster is shared with the compactor workload, which writes and compacts it), then, on a
// failure-free history that shows none, Kubernetes' own checker (realCheck), as the driver's Check
// does. Client c's operations are made
// by API server c mod A (A API server machines), each client at its own address on that machine
// (one remote.Serve each), so that an API server serves several clients at once, as the driver's
// one store serves all of them.

import (
	"fmt"
	"sync/atomic"
	"time"

	"github.com/anishathalye/porcupine"
	"go.uber.org/zap"
	"google.golang.org/grpc"

	clientv3 "go.etcd.io/etcd/client/v3"
	"go.etcd.io/etcd/client/v3/kubernetes"

	"github.com/mit-pdos/etcd-grove/examples/etcd/dist/client"
	"github.com/mit-pdos/etcd-grove/examples/lib/etcdstart"
	"github.com/mit-pdos/etcd-grove/examples/lib/lintest"
	"github.com/mit-pdos/etcd-grove/examples/lib/remote"

	k8s "github.com/mit-pdos/etcd-grove/examples/k8s/etcd3"
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
// (etcdstart's timeouts and keepalive, the default retries), with no proxy (grpc.WithNoProxy, as
// etcdstart.NewClients and etcd-dist's clients: every connection goes to an endpoint of eps),
// trying until it succeeds.
func newKubeClient(eps []string) *kubernetes.Client {
	for {
		kc, err := kubernetes.New(clientv3.Config{
			Endpoints:            eps,
			DialTimeout:          etcdstart.DialTimeout,
			DialKeepAliveTime:    etcdstart.KeepAliveTime,
			DialKeepAliveTimeout: etcdstart.KeepAliveTimeout,
			Logger:               zap.NewNop(),
			DialOptions:          []grpc.DialOption{grpc.WithNoProxy()},
		})
		if err == nil {
			return kc
		}
		time.Sleep(100 * time.Millisecond)
	}
}

// StoreNode is API server machine a of the store workload w: its store (the driver's, without the
// seeds: etcd3.NewStoreOnly) over a kubernetes client of eps from member a on, then, for every
// client c with c mod A = a, remote.Serve at addrs[c] whose operation is the driver's call (or
// runWatch) through that store. It never returns.
func StoreNode(w Workload, a int, addrs []string, eps []string) {
	kc := newKubeClient(client.Rotate(eps, a))
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
// driver's seed, at whatever revisions the shared cluster gives them: etcd3.SeedShared), waits
// for its API server machines, calls ready, then runs the driver's clients (lintest.RunLin2's
// clients, its check left to here) with the operations made at the API servers (remote.Do at
// addrs[c] for client c), the per-client cache kept here (etcd3.Record, Apply's bookkeeping),
// and checks the history: porcupine against the driver's Model with foreign revisions
// (etcd3.SharedModel: the compactor workload writes the same cluster), then Kubernetes' checker
// where it applies. It panics if porcupine finds the history not linearizable, if Kubernetes'
// checker rejects a history it applies to, or on an etcd "compacted" error from an operation that
// reads at no old revision.
//
// A "compacted" error (the compactor workload compacts the cluster while the store serves) is
// accepted on an operation at an explicit old revision (etcd3.PastRead: a List at its resource
// version, a watch from one) and on one at a revision the store fixed at an earlier read of its
// own (etcd3.PinnedRead: a paged List's later pages; a watch from the most recent revision,
// which the store reads first, or after its list for a watch-list, and whose stream the etcd client
// resumes from its last revision), and nowhere else (a Get, a write, a List of one page: each
// reads at the latest revision, which compaction never passes). Its outcome tells nothing: a List's is the driver's failed read (EOther, which
// constrains nothing), a watch's Error event is dropped as Model drops every Error event (the
// events before it are checked as always). Kubernetes' checker is defined on histories without a
// failed call, and is skipped in a run with a "compacted" error.
func RunStore(w Workload, eps []string, addrs []string, obs Observer) Result {
	if !k8s.SetFeatures() {
		return ended("the features could not be set")
	}
	cli, err := etcdstart.NewClients(eps, zap.NewNop())
	if err != nil {
		return ended("no client")
	}
	seeded, ok := k8s.SeedShared(cli)
	cli.Close()
	if !ok {
		return ended("the seeds failed")
	}
	if !client.AwaitAccept(addrs) {
		return ended("an API server machine never answered")
	}
	obs.Ready()
	tbl := seeded.NewCache(w.Clients, w.Ops)
	var rawLost atomic.Bool
	var past, pinned atomic.Int64
	codec := StoreCodec()
	apply := func(input any) any {
		in := input.(k8s.Input)
		so := remote.Do(addrs[in.Client], in, codec, StoreAttempt).(StoreOut)
		if so.Compacted {
			switch {
			case k8s.PastRead(in):
				past.Add(1)
			case k8s.PinnedRead(in):
				pinned.Add(1)
			default:
				panic(fmt.Sprintf("k8sdist: a compacted error on an operation at no old revision: "+
					"kind %d, resource version %q, match %d, limit %d, send-initial-events %d",
					in.Kind, in.MinRV, in.Match, in.Limit, in.SendInit))
			}
		}
		k8s.Record(tbl, in, so.Out)
		if !so.RawOK {
			rawLost.Store(true)
		}
		return so.Out
	}
	gen := func(id int) any { return k8s.Gen(tbl, id) }
	_, lops := lintest.RunLin2(k8s.AcceptAll(), apply, gen, lintest.CounterClock(), w.Clients, w.Ops,
		w.Watchers, w.WOps, CheckTimeout)
	comp := ""
	if n := past.Load() + pinned.Load(); n > 0 {
		comp = "; " + itoa(int(n)) + " compacted errors accepted (" + itoa(int(past.Load())) +
			" at an explicit old revision, " + itoa(int(pinned.Load())) + " at a pinned one)"
	}
	if obs.History != nil {
		obs.History(seeded, lops)
	}
	revs := k8s.HistoryRevs(lops)
	r, mode := CheckShared(seeded, revs, lops, CheckTimeout)
	full := ""
	if mode != k8s.Lazy {
		full = "; decided by the " + []string{"lazy", "eager", "full"}[mode] + " model"
	}
	if r == porcupine.Illegal {
		panic("k8sdist: porcupine found the store's history not linearizable")
	}
	if r != porcupine.Ok {
		return ended("porcupine timed out" + full + comp)
	}
	if past.Load()+pinned.Load() > 0 {
		return Result{Checked: true, Why: "model only: Kubernetes' checker skipped, a compacted error" + full + comp}
	}
	if !k8s.FailureFree(lops) {
		return Result{Checked: true, Why: "model only: a call failed" + full}
	}
	if rawLost.Load() {
		return Result{Checked: true, Why: "model only: a raw answer did not cross the wire" + full}
	}
	if !seeded.NoForeign(lops) {
		return Result{Checked: true, Why: "model only: Kubernetes' checker skipped, foreign revisions (its model numbers the revisions itself)" + full}
	}
	rr := seeded.RealCheck(lops, CheckTimeout)
	if rr == porcupine.Illegal {
		panic("k8sdist: Kubernetes' checker rejected the store's history")
	}
	if rr != porcupine.Ok {
		return Result{Checked: true, Why: "model only: Kubernetes' checker timed out" + full}
	}
	return Result{Checked: true, Why: "model and Kubernetes' checker" + full}
}

// CheckShared checks the store history ops against SharedModel (revs its HistoryRevs): the lazy
// model, and on Illegal the eager one, and on Illegal the full one, whose Illegal is the verdict
// (each mode complete where the one before is not); each with the timeout timeout. It returns the
// verdict and the mode that gave it.
func CheckShared(seeded k8s.Seeded, revs k8s.Revs, ops []porcupine.Operation, timeout time.Duration) (porcupine.CheckResult, int) {
	for mode := k8s.Lazy; ; mode++ {
		r := porcupine.CheckOperationsTimeout(seeded.SharedModel(revs, mode), ops, timeout)
		if r != porcupine.Illegal || mode == k8s.Full {
			return r, mode
		}
	}
}
