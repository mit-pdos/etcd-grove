// Package counter is an instance of the lintest driver: a counter under a mutex (a
// linearizable library), its porcupine model, and a check of it with lintest.Run. The proof
// (Proof/github_com/mit_pdos/etcd_grove/examples/lintest/counter/) shows Check never returns
// porcupine.Illegal: the driver's premises are met by a real library and model.
package counter

import (
	"sync"
	"time"

	"github.com/anishathalye/porcupine"
	"github.com/mit-pdos/etcd-grove/examples/lintest"
)

// Inc is the counter's increment input; any other input is a read.
//
// The operation is chosen by the input's dynamic type only (`_, inc := input.(Inc)`), never by
// its value: lintest.Run's apply must take any input, and its proof's inputs are arbitrary
// interface values.
type Inc struct{}

// Read is the input clients use for a read (any input other than Inc is one).
type Read struct{}

// Model is the counter's sequential specification: the state is an int64; an input Inc
// increments it and outputs the new value, any other input outputs it.
func Model() porcupine.Model {
	return porcupine.Model{
		Init: func() any { return int64(0) },
		Step: func(state, input, output any) (bool, any) {
			s := state.(int64)
			_, inc := input.(Inc)
			if inc {
				return output.(int64) == s+1, s + 1
			}
			return output.(int64) == s, s
		},
		Equal: func(a, b any) bool { return a.(int64) == b.(int64) },
	}
}

// A Counter is an int64 under a mutex.
type Counter struct {
	mu sync.Mutex
	n  int64
}

func New() *Counter {
	return &Counter{}
}

// Apply runs one operation: an input Inc increments the counter and returns the new value,
// any other input returns it.
func (c *Counter) Apply(input any) any {
	_, inc := input.(Inc)
	c.mu.Lock()
	if inc {
		c.n = c.n + 1
	}
	n := c.n
	c.mu.Unlock()
	return n
}

// Check runs clients clients of a fresh counter, each running ops operations (client i
// increments if i is even and reads otherwise), traced with the given clock, and checks the
// trace with porcupine.
func Check(clock lintest.Clock, clients int, ops int, timeout time.Duration) porcupine.CheckResult {
	c := New()
	gen := func(id int) any {
		if id%2 == 0 {
			return Inc{}
		}
		return Read{}
	}
	return lintest.Run(Model(), c.Apply, gen, clock, clients, ops, timeout)
}
