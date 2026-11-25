package counter

import (
	"testing"

	"github.com/anishathalye/porcupine"
	"github.com/goose-lang/primitive"
	"github.com/mit-pdos/etcd-grove/examples/lib/lintest"
)

func TestCheck(t *testing.T) {
	for _, clock := range []lintest.Clock{lintest.MonotonicClock(), lintest.CounterClock()} {
		if r := Check(clock, 6, 40, 0); r != porcupine.Ok {
			t.Fatalf("got %v", r)
		}
	}
}

func TestMainPasses(t *testing.T) {
	Main()
}

// gen is Check's generator: an increment or a read, at random.
func gen(int) any { return primitive.RandomUint64()%2 == 0 }

// mainPanics runs Main's check -- lintest.Run on the package's model with Check's random
// generator, MaxClients clients of MaxOps operations, a counter clock, no timeout, and a panic
// unless porcupine answers Ok -- over the library apply, and reports whether it panicked.
func mainPanics(apply func(any) any) (panicked bool) {
	defer func() { panicked = recover() != nil }()
	if r := lintest.Run(Model(), apply, gen, lintest.CounterClock(), MaxClients, MaxOps, 0); r != porcupine.Ok {
		panic("porcupine rejected the trace")
	}
	return false
}

// TestMainCheckFires is the negative control of Main's check: over the real counter it never
// fires, and over a mutant whose reads return -1 (a value the counter never holds) it panics, so
// the check Main's proof shows never fires is reachable.
func TestMainCheckFires(t *testing.T) {
	if mainPanics(New().Apply) {
		t.Fatal("Main's check fired on the real counter")
	}
	c := New()
	mutant := func(input any) any {
		if !input.(bool) {
			c.Apply(input)
			return int64(-1)
		}
		return c.Apply(input)
	}
	if !mainPanics(mutant) {
		t.Fatal("Main's check did not fire on a counter whose reads return -1")
	}
}
