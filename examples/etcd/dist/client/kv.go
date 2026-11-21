package client

import (
	"sync"
	"time"

	"github.com/anishathalye/porcupine"

	clientv3 "go.etcd.io/etcd/client/v3"

	"github.com/mit-pdos/etcd-grove/examples/etcd/txnlin"
	"github.com/mit-pdos/etcd-grove/examples/lib/lintest"
)

// The kv workload (txnlinfaultsN's Main minus its start and partitioner; Lean: Workload.kv):
// clients concurrent clients, each running ops of txnlin's operations (gets, lists, puts, deletes,
// transactions and compare-and-sets of the keys k0, k1, k2) through a clientv3 client of its own,
// the history checked by porcupine against txnlin's model, which starts from an empty store at
// revision 1 (hence: the deployment's only workload writing keys) and lets a failed write take
// effect at any later time, or never (the error rule). Panics if porcupine finds the history
// illegal.
//
// Structure (the seam for Remote): kvApply is a client node's whole job (one operation through its
// own client); kvClient is the orchestrator's loop for one client (lintest's runClient, copied:
// lintest.Run's apply has no client id, so it cannot send client i's operations through client
// i's own clientv3 client); RunKV makes the clients, runs the loops and checks the history.

// kvCheckTimeout bounds porcupine's search: an answer it does not reach in time is Unknown, which
// is not a failure (the theorem is that the answer is never Illegal).
const kvCheckTimeout = 2 * time.Minute

// kvApply is client node i's operation: one of txnlin's operations through its own client cli
// (txnlin.Apply: an error makes the output Err, an unknown outcome).
func kvApply(cli *clientv3.Client) func(any) any {
	return func(input any) any {
		return txnlin.Apply(cli, input)
	}
}

// kvClient runs ops operations of client id (txnlin.Gen(id)) through apply, one after the other,
// and returns their trace (lintest's runClient, copied).
func kvClient(id int, ops int, apply func(any) any, clock lintest.Clock) []porcupine.Operation {
	var history []porcupine.Operation
	for i := 0; i < ops; i++ {
		input := txnlin.Gen(id)
		call := clock()
		output := apply(input)
		ret := clock()
		history = append(history, porcupine.Operation{
			ClientId: id,
			Input:    input,
			Call:     call,
			Output:   output,
			Return:   ret,
		})
	}
	return history
}

// RunKV runs the kv workload (see above) against the endpoints eps: client i's clientv3 client is
// of every endpoint, preferring eps[i mod k].
func RunKV(eps []string, clients int, ops int) Result {
	clis := make([]*clientv3.Client, clients)
	for i := 0; i < clients; i++ {
		cli, err := newClient(rotate(eps, i))
		if err != nil {
			return ended("kv: a client failed to connect")
		}
		clis[i] = cli
	}
	clock := lintest.CounterClock()
	histories := make([][]porcupine.Operation, clients)
	var wg sync.WaitGroup
	for i := 0; i < clients; i++ {
		wg.Add(1)
		go func() {
			histories[i] = kvClient(i, ops, kvApply(clis[i]), clock)
			wg.Done()
		}()
	}
	wg.Wait()
	for _, cli := range clis {
		cli.Close()
	}
	var history []porcupine.Operation
	for _, h := range histories {
		history = append(history, h...)
	}
	r := porcupine.CheckOperationsTimeout(txnlin.Model(), history, kvCheckTimeout)
	if r == porcupine.Illegal {
		panic("dist kv: porcupine found the history not linearizable")
	}
	if r != porcupine.Ok {
		return ended("kv: porcupine timed out (Unknown)")
	}
	return checked()
}
