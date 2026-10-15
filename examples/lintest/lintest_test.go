package lintest

import (
	"math/rand"
	"sync"
	"testing"
	"time"

	"github.com/anishathalye/porcupine"
)

// An increment-or-read counter: input true increments and returns the new value, false
// reads it.
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

func gen(int) any { return rand.Intn(2) == 0 }

// A counter under a mutex.
func newCounter() func(any) any {
	var mu sync.Mutex
	n := 0
	return func(input any) any {
		mu.Lock()
		defer mu.Unlock()
		if input.(bool) {
			n++
		}
		return n
	}
}

func TestLinearizableCounter(t *testing.T) {
	for _, clock := range []Clock{MonotonicClock(), CounterClock()} {
		if r := Run(counterModel, newCounter(), gen, clock, 4, 50, 0); r != porcupine.Ok {
			t.Fatalf("got %v", r)
		}
	}
}

// A counter whose increment is not atomic (a read, a yield, a write) loses increments,
// which porcupine finds.
func TestRacyCounter(t *testing.T) {
	var mu sync.Mutex
	n := 0
	apply := func(input any) any {
		mu.Lock()
		v := n
		mu.Unlock()
		if !input.(bool) {
			return v
		}
		time.Sleep(time.Microsecond)
		mu.Lock()
		n = v + 1
		mu.Unlock()
		return v + 1
	}
	inc := func(int) any { return true }
	if r := Run(counterModel, apply, inc, CounterClock(), 8, 20, 10*time.Second); r != porcupine.Illegal {
		t.Fatalf("got %v", r)
	}
}
