package client

import (
	"time"

	"github.com/anishathalye/porcupine"

	"github.com/mit-pdos/etcd-grove/examples/etcd/dist/kvremote"
	"github.com/mit-pdos/etcd-grove/examples/lib/robust"
)

// The kv workload (txnlinfaultsN's Main minus its start and partitioner; Lean: Workload.kv): one
// client machine per client (kvremote.Node, each with a clientv3 client of its own) and this
// orchestrator (kvremote.Orch: remote.Run), each client running ops of txnlin's operations (gets,
// lists, puts, deletes, transactions and compare-and-sets of the keys k0, k1, k2) at its machine,
// the history checked by porcupine against txnlin's model, which starts from an empty store at
// revision 1 (hence: the deployment's only workload writing keys) and lets a failed write take
// effect at any later time, or never (the error rule: an error at the client machine, or a call to
// it without an answer). Panics if porcupine finds the history illegal.

// kvCheckTimeout bounds porcupine's search: an answer it does not reach in time is Unknown, which
// is not a failure (the theorem is that the answer is never Illegal).
const kvCheckTimeout = 2 * time.Minute

// RunKV runs the kv workload (see above) with the client machines nodes (client c's at nodes[c],
// its clientv3 client of every endpoint, preferring eps[c mod k]); its set-up is the wait for
// them (ready after it).
func RunKV(nodes []string, ops int, ready func()) Result {
	if !robust.AwaitAccept(nodes) {
		return ended("kv: a client machine never answered")
	}
	ready()
	r := kvremote.Orch(nodes, ops, kvCheckTimeout)
	if r == porcupine.Illegal {
		panic("dist kv: porcupine found the history not linearizable")
	}
	if r != porcupine.Ok {
		return ended("kv: porcupine timed out (Unknown)")
	}
	return checked()
}
