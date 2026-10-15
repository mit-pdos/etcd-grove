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

// Model is the counter's sequential specification: the state is an int64; the input true
// increments it and outputs the new value, false outputs it.
func Model() porcupine.Model {
	return porcupine.Model{
		Init: func() any { return int64(0) },
		Step: func(state, input, output any) (bool, any) {
			s := state.(int64)
			if input.(bool) {
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

// Apply runs one operation: the input true increments the counter and returns the new value,
// false returns it.
func (c *Counter) Apply(input any) any {
	c.mu.Lock()
	if input.(bool) {
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
	gen := func(id int) any { return id%2 == 0 }
	return lintest.Run(Model(), c.Apply, gen, clock, clients, ops, timeout)
}
