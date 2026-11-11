// Package lintest is a generic driver for porcupine: concurrent clients run a library's
// operations, each traced the way etcd's robustness tests trace etcd's requests
// (tests/robustness/model/history.go: a porcupine.Operation per request, with the client's
// stream id and the call and return timestamps of a monotonic clock read just before the
// request and just after its response), and the trace is checked by porcupine as etcd
// checks it (tests/robustness/validate/operations.go: CheckOperationsVerbose with a
// timeout).
//
// The library is a closure `apply` from an operation's input to its output; the inputs are
// chosen by `gen` (e.g. randomly, as etcd's traffic generators do). The proof
// (Proof/github_com/mit_pdos/etcd_grove/examples/lib/lintest/) shows that if `apply` is
// logically atomic against porcupine's model, Run never returns porcupine.Illegal.
package lintest

import (
	"sync"
	"sync/atomic"
	"time"

	"github.com/anishathalye/porcupine"
)

// A Clock returns a timestamp, in nanoseconds; successive readings never decrease.
type Clock func() int64

// MonotonicClock is the clock of etcd's robustness tests: the time since a base, by Go's
// monotonic clock (time.Since).
func MonotonicClock() Clock {
	base := time.Now()
	return func() int64 {
		return time.Since(base).Nanoseconds()
	}
}

// CounterClock is a logical clock: each reading is one more than the one before.
func CounterClock() Clock {
	t := new(atomic.Int64)
	return func() int64 {
		return t.Add(1)
	}
}

// runClient runs ops operations of the library from client id, one after the other, and
// returns their trace.
func runClient(id int, ops int, gen func(int) any, apply func(any) any, clock Clock) []porcupine.Operation {
	var history []porcupine.Operation
	for i := 0; i < ops; i++ {
		input := gen(id)
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

// Run runs clients clients concurrently, each running ops operations of the library, and
// checks their trace against model with porcupine (RunLin, without the linearization).
func Run(model porcupine.Model, apply func(any) any, gen func(int) any, clock Clock, clients int, ops int, timeout time.Duration) porcupine.CheckResult {
	r, _ := RunLin(model, apply, gen, clock, clients, ops, timeout)
	return r
}

// orderByLinearization returns the operations ops at the indices linearization, in its order
// (Kubernetes' TestCorrectness's orderByLinearization).
func orderByLinearization(ops []porcupine.Operation, linearization []int) []porcupine.Operation {
	ordered := make([]porcupine.Operation, len(linearization))
	for i, idx := range linearization {
		ordered[i] = ops[idx]
	}
	return ordered
}

// RunLin runs clients clients concurrently, each running ops operations of the library, and
// checks their trace against model with porcupine. When porcupine answers Ok, it also returns the
// trace's operations in the order of the linearization porcupine found, as Kubernetes'
// TestCorrectness reads it (test/integration/apiserver/storage/correctness_test.go: the model
// has no Partition, so the info's one partition holds one complete linearization, of indices
// into the trace); otherwise nil.
func RunLin(model porcupine.Model, apply func(any) any, gen func(int) any, clock Clock, clients int, ops int, timeout time.Duration) (porcupine.CheckResult, []porcupine.Operation) {
	return RunLin2(model, apply, gen, clock, clients, ops, 0, 0, timeout)
}

// groupOps is the number of operations client id runs: ops in the first group (id < clients),
// ops2 in the second.
func groupOps(id int, clients int, ops int, ops2 int) int {
	if id < clients {
		return ops
	}
	return ops2
}

// RunLin2 is RunLin with two groups of clients: clients 0 to clients-1 run ops operations each,
// clients clients to clients+clients2-1 run ops2 each (notes/k8s-7f-scope.md: the k8s driver's
// watchers, whose operations are whole watches, beside its unary clients).
func RunLin2(model porcupine.Model, apply func(any) any, gen func(int) any, clock Clock, clients int, ops int, clients2 int, ops2 int, timeout time.Duration) (porcupine.CheckResult, []porcupine.Operation) {
	histories := make([][]porcupine.Operation, clients+clients2)
	var wg sync.WaitGroup
	for id := 0; id < clients+clients2; id++ {
		n := groupOps(id, clients, ops, ops2)
		wg.Add(1)
		go func() {
			histories[id] = runClient(id, n, gen, apply, clock)
			wg.Done()
		}()
	}
	wg.Wait()
	var operations []porcupine.Operation
	for _, h := range histories {
		operations = append(operations, h...)
	}
	result, info := porcupine.CheckOperationsVerbose(model, operations, timeout)
	if result != porcupine.Ok {
		return result, nil
	}
	linearizations := info.PartialLinearizations()
	// an empty trace has no linearization in the info (porcupine collects none)
	if len(linearizations) != 1 || len(linearizations[0]) == 0 {
		return result, nil
	}
	return result, orderByLinearization(operations, linearizations[0][0])
}
