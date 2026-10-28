package logkvsnap

import (
	"testing"

	"github.com/anishathalye/porcupine"
	"github.com/mit-pdos/etcd-grove/examples/lintest"
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
