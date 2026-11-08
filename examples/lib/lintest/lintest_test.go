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

// RunLin's linearization is the whole trace, in an order the model accepts from its initial
// state, respecting real time; an empty trace has the empty one.
func TestRunLinCounter(t *testing.T) {
	r, lin := RunLin(counterModel, newCounter(), gen, CounterClock(), 4, 50, 0)
	if r != porcupine.Ok || len(lin) != 200 {
		t.Fatalf("got %v, %d operations", r, len(lin))
	}
	s := counterModel.Init()
	for i, op := range lin {
		ok, next := counterModel.Step(s, op.Input, op.Output)
		if !ok {
			t.Fatalf("operation %d of the linearization refused", i)
		}
		s = next
		for _, later := range lin[i+1:] {
			if later.Return < op.Call {
				t.Fatalf("operation %d precedes an earlier one in real time", i)
			}
		}
	}
	if r, lin := RunLin(counterModel, newCounter(), gen, CounterClock(), 0, 10, 0); r != porcupine.Ok || len(lin) != 0 {
		t.Fatalf("empty trace: %v, %d", r, len(lin))
	}
}

// RunLin2 runs both groups: clients ops operations each, clients2 ops2 each, with each client's
// id (gen sees the second group's ids from clients on), and linearizes all of them.
func TestRunLin2Counter(t *testing.T) {
	var mu sync.Mutex
	perID := map[int]int{}
	g := func(id int) any {
		mu.Lock()
		perID[id]++
		mu.Unlock()
		return rand.Intn(2) == 0
	}
	r, lin := RunLin2(counterModel, newCounter(), g, CounterClock(), 3, 20, 2, 7, 0)
	if r != porcupine.Ok || len(lin) != 3*20+2*7 {
		t.Fatalf("got %v, %d operations", r, len(lin))
	}
	for id := 0; id < 5; id++ {
		want := 20
		if id >= 3 {
			want = 7
		}
		if perID[id] != want {
			t.Fatalf("client %d ran %d operations, want %d", id, perID[id], want)
		}
	}
	if r, lin := RunLin2(counterModel, newCounter(), gen, CounterClock(), 0, 5, 0, 5, 0); r != porcupine.Ok || len(lin) != 0 {
		t.Fatalf("empty trace: %v, %d", r, len(lin))
	}
}
