package perclient

import (
	"math/rand"
	"sync"
	"testing"
	"time"

	"github.com/anishathalye/porcupine"
	"github.com/mit-pdos/etcd-grove/examples/lib/lintest"
)

// An increment-or-read counter: input true increments and returns the new value, false reads it.
var counterModel = porcupine.Model{
	Init: func() any { return 0 },
	Step: func(state, input, output any) (bool, any) {
		s := state.(int)
		if input.(bool) {
			return output.(int) == s+1, s + 1
		}
		return output.(int) == s, s
	},
	Equal: func(a, b any) bool { return a.(int) == b.(int) },
}

// apply is told every client's id, and the trace is checked as lintest.Run's.
func TestCounter(t *testing.T) {
	var mu sync.Mutex
	n := 0
	seen := map[int]bool{}
	apply := func(id int, input any) any {
		mu.Lock()
		defer mu.Unlock()
		seen[id] = true
		if input.(bool) {
			n++
		}
		return n
	}
	gen := func(int) any { return rand.Intn(2) == 0 }
	if r := Run(counterModel, apply, gen, lintest.CounterClock(), 3, 30, 0); r != porcupine.Ok {
		t.Fatalf("got %v", r)
	}
	if len(seen) != 3 {
		t.Fatalf("ids seen %v", seen)
	}
}

// A racy library is caught.
func TestRacyCounter(t *testing.T) {
	var mu sync.Mutex
	n := 0
	apply := func(id int, input any) any {
		mu.Lock()
		v := n
		mu.Unlock()
		time.Sleep(time.Microsecond)
		mu.Lock()
		n = v + 1
		mu.Unlock()
		return v + 1
	}
	inc := func(int) any { return true }
	if r := Run(counterModel, apply, inc, lintest.CounterClock(), 8, 20, 10*time.Second); r != porcupine.Illegal {
		t.Fatalf("got %v", r)
	}
}
