package client

import (
	"github.com/anishathalye/porcupine"

	"github.com/mit-pdos/etcd-grove/examples/etcd/dist/kvremote"
)

// The kv workload (txnlinfaultsN's Main minus its start and partitioner; Lean: Workload.kv): one
// client machine per client (kvremote.Node, each with a clientv3 client of its own) and this
// orchestrator (kvremote.Orch: remote.Run), each client running ops of txnlin's operations (gets,
// lists, puts, deletes, transactions and compare-and-sets of the keys k0, k1, k2) at its machine,
// the history checked by porcupine against txnlin's model, which starts from an empty store at
// revision 1 (hence: the deployment's only workload writing keys) and lets a failed write take
// effect at any later time, or never (the error rule: an error at the client machine, or a call to
// it without an answer). Panics if porcupine finds the history illegal.

// RunKV runs the kv workload (see above) with the client machines nodes (client c's at nodes[c],
// its clientv3 client of every endpoint, preferring eps[c mod k]); no set-up (ready at once). A
// client machine that is not listening yet is a call without an answer (no wait: the harness starts
// the orchestrator once its client machines listen). Porcupine's search has no timeout (0): the check
// always runs to its verdict, Ok or Illegal. The Unknown branch below is kept (porcupine returns
// Unknown only on a timeout, which a timeout of 0 never sets; the proof does not rely on that).
func RunKV(nodes []string, ops int, ready func()) Result {
	ready()
	r := kvremote.Orch(nodes, ops, 0)
	if r == porcupine.Illegal {
		panic("dist kv: porcupine found the history not linearizable")
	}
	if r != porcupine.Ok {
		return ended("kv: porcupine timed out (Unknown)")
	}
	return checked()
}
