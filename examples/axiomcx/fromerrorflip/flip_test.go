// The fromerror-wand counterexample (etcd-grove-03's attack on T8, 2026-11-18; notes/fromerror-wand.md):
// status.FromError.wp_proof's post wand `errorMsgIs e m -∗ ⌜errDesc err = m⌝` accepts an errorMsgIs
// proved after the call; an Error() that diverges after the call satisfies errorMsgIs for every m.
package fromerrorflip

import (
	"sync/atomic"
	"testing"
	"time"

	"google.golang.org/grpc/status"
)

// flipErr: a leaf error (no Unwrap/As/Is/GRPCStatus/Format) whose Error() returns "A" while on,
// and loops forever once off. errorMsgIs e "A" holds of it from the start (each call returns "A"
// or diverges); once off, errorMsgIs e m holds for EVERY m (each call diverges).
type flipErr struct{ on *atomic.Bool }

func (f flipErr) Error() string {
	if f.on.Load() {
		return "A"
	}
	for {
	}
}

// Main: what the counterexample program does. FromError's post (ok = false) wand
// `errorMsgIs e m -∗ errDesc err = m` applied to errorMsgIs e "B" and errorMsgIs e "C",
// both provable after the switch, gives "B" = "C", so the proof discharges the panic.
func Main() {
	f := flipErr{on: new(atomic.Bool)}
	f.on.Store(true)
	_, ok := status.FromError(f)
	if !ok {
		f.on.Store(false)
		panic("unreachable per FromError.spec")
	}
}

func TestFlip(t *testing.T) {
	f := flipErr{on: new(atomic.Bool)}
	f.on.Store(true)
	s, ok := status.FromError(f)
	t.Logf("FromError: ok=%v msg=%q", ok, s.Message())
	f.on.Store(false)
	done := make(chan struct{})
	go func() { _ = f.Error(); close(done) }()
	select {
	case <-done:
		t.Fatal("Error() returned after the switch")
	case <-time.After(200 * time.Millisecond):
		t.Log("Error() diverges after the switch")
	}
	defer func() { t.Logf("Main panicked: %v", recover()) }()
	Main()
}
