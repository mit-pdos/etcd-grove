package logkvsnap

import (
	"testing"

	"github.com/anishathalye/porcupine"
	"github.com/goose-lang/primitive"
	"github.com/mit-pdos/etcd-grove/examples/lib/lintest"
)

func TestCheck(t *testing.T) {
	for _, clock := range []lintest.Clock{lintest.MonotonicClock(), lintest.CounterClock()} {
		for i := 0; i < 20; i++ {
			if r := Check(clock, 8, 50, 0); r != porcupine.Ok {
				t.Fatalf("porcupine answered %v", r)
			}
		}
	}
}

func TestMain_(t *testing.T) { Main() }

var vals = []string{"a", "b", "c", "d", "e", "f", "g", "h"}

// gen is Check's generator: a write of one of eight values or a read, at random.
func gen(int) any {
	return Op{Put: primitive.RandomUint64()%2 == 0, Val: vals[primitive.RandomUint64()%8]}
}

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

// TestMainCheckFires is the negative control of Main's check: over the real server it never
// fires, and over a mutant whose reads return a value no write writes it panics, so the check
// Main's proof shows never fires is reachable.
func TestMainCheckFires(t *testing.T) {
	if mainPanics(New().Apply) {
		t.Fatal("Main's check fired on the real server")
	}
	s := New()
	mutant := func(input any) any {
		out := s.Apply(input)
		if !input.(Op).Put {
			return "mutant"
		}
		return out
	}
	if !mainPanics(mutant) {
		t.Fatal("Main's check did not fire on a server whose reads return a value never written")
	}
}
