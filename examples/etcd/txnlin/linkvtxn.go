// Package txnlin is the lintest driver instantiated with etcd over the KV API etcd's robustness
// tester drives (notes/linkv-txn-plan.md, stage D): one etcd member started in-process (as
// examples/etcd/putget does), a client connected to it, and lintest.Run with concurrent clients doing
// gets, lists, puts, deletes, multi-operation transactions and compare-and-sets of a few keys,
// checked by porcupine against a model of etcd's KV (txnwork.Model). Main panics if porcupine finds
// the history not linearizable; the theorem to prove is that it does not.
//
// The workload, its model and Apply are the library examples/lib/txnwork's (moved there verbatim,
// 2026-11-27, so that the multi-machine example imports no single-process driver).
package txnlin

import (
	"time"

	"github.com/anishathalye/porcupine"
	"go.uber.org/zap"

	clientv3 "go.etcd.io/etcd/client/v3"

	"github.com/mit-pdos/etcd-grove/examples/lib/etcdstart"
	"github.com/mit-pdos/etcd-grove/examples/lib/lintest"
	"github.com/mit-pdos/etcd-grove/examples/lib/txnwork"
)

// Check runs lintest.Run of clients concurrent clients of cli, each running ops operations, and
// returns porcupine's verdict.
func Check(cli *clientv3.Client, clients int, ops int, timeout time.Duration) porcupine.CheckResult {
	apply := func(input any) any { return txnwork.Apply(cli, input) }
	return lintest.Run(txnwork.Model(), apply, txnwork.Gen, lintest.CounterClock(), clients, ops, timeout)
}

// The client address: the string net.Listen is given is the client's endpoint, verbatim (a plain
// host:port, no scheme). Not the other examples', so that their tests can run at once.
const clientAddr = "127.0.0.1:23796"

// Main starts one member of a new cluster (as examples/linkv's Main does), connects a client
// with etcd's default configuration and runs Check; it panics if porcupine finds the history
// illegal. An error from a step before Check ends Main without a check.
func Main(clients int, ops int) porcupine.CheckResult {
	lg := zap.NewNop()
	s, err := etcdstart.StartServer("linkvtxn", "127.0.0.1:23806", clientAddr, lg)
	if err != nil {
		return porcupine.Unknown
	}
	if err := etcdstart.Serve(s, clientAddr); err != nil {
		return porcupine.Unknown
	}

	// etcd's default client configuration (its default retries): the server never answers with a
	// refusal (authentication off, a voter), so a write is sent at most once and the server applies
	// it at most once, while a read may be retried (decision D29).
	cli, err := etcdstart.NewClient(clientAddr, lg)
	if err != nil {
		return porcupine.Unknown
	}
	r := Check(cli, clients, ops, 0)
	if r == porcupine.Illegal {
		panic("linkvtxn: porcupine found the history not linearizable")
	}
	return r
}
