// Package perclient is lintest's driver with an apply that is told which client calls it:
// Run(model, apply, ...) is lintest.Run with apply(id, input) running client id's operation (e.g.
// through client id's own connection, or at client id's own machine: examples/lib/remote).
//
// A package of its own, beside lintest, so that lintest's translation, and the proofs over it,
// stay as they are (notes/remote-port-plan.md, Q1).
package perclient

import (
	"sync"
	"time"

	"github.com/anishathalye/porcupine"
	"github.com/mit-pdos/etcd-grove/examples/lib/lintest"
)

// runClient runs ops operations of client id, one after the other, and returns their trace
// (lintest's runClient, with apply told the id).
func runClient(id int, ops int, gen func(int) any, apply func(int, any) any, clock lintest.Clock) []porcupine.Operation {
	var history []porcupine.Operation
	for i := 0; i < ops; i++ {
		input := gen(id)
		call := clock()
		output := apply(id, input)
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

// Run runs clients clients concurrently, each running ops operations through apply(id, ·), and
// checks their trace against model with porcupine (lintest.Run's, with apply told the id).
func Run(model porcupine.Model, apply func(int, any) any, gen func(int) any, clock lintest.Clock, clients int, ops int, timeout time.Duration) porcupine.CheckResult {
	histories := make([][]porcupine.Operation, clients)
	var wg sync.WaitGroup
	for id := 0; id < clients; id++ {
		wg.Add(1)
		go func() {
			histories[id] = runClient(id, ops, gen, apply, clock)
			wg.Done()
		}()
	}
	wg.Wait()
	var operations []porcupine.Operation
	for _, h := range histories {
		operations = append(operations, h...)
	}
	result, _ := porcupine.CheckOperationsVerbose(model, operations, timeout)
	return result
}
