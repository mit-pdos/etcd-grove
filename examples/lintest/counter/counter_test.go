package counter

import (
	"testing"

	"github.com/anishathalye/porcupine"
	"github.com/mit-pdos/etcd-grove/examples/lintest"
)

func TestCheck(t *testing.T) {
	for _, clock := range []lintest.Clock{lintest.MonotonicClock(), lintest.CounterClock()} {
		if r := Check(clock, 6, 40, 0); r != porcupine.Ok {
			t.Fatalf("got %v", r)
		}
	}
}
