package kvraft

import (
	"context"
	"net"
	"sync"
	"time"
)

// Timeouts without the clock. The package never reads the time (time.Now, a connection's
// deadline, context.WithTimeout's deadline): Perennial's model of time only axiomatizes the clock,
// and kvraft's top-level theorem rests on no axiom of it (notes/kvraft-proof-plan.md, decision D;
// as examples/raft/kvdurablenoax). A timeout is a timer instead (time.AfterFunc), which cancels a
// context or closes a connection.

// withTimeout is context.WithTimeout(context.Background(), d) without a deadline: a context that
// a timer cancels after d, or the cancel function returned before (kvdurablenoax's). Nothing here
// reads a context's deadline or tells context.Canceled from context.DeadlineExceeded. cancel does
// not stop the timer: firing later, it cancels a canceled context, which does nothing.
func withTimeout(d time.Duration) (context.Context, context.CancelFunc) {
	ctx, cancel := context.WithCancel(context.Background())
	time.AfterFunc(d, cancel)
	return ctx, cancel
}

// connTimer is closeAfter's state: whether its time is up or it was disarmed, whichever came
// first.
type connTimer struct {
	mu   sync.Mutex
	over bool // the timer fired, or was disarmed
}

// closeAfter is a connection deadline d from now, as a timer: unless disarmed first, it closes c
// after d, which fails the read or write in progress on c, and every later one. The returned
// function disarms it and says whether it did so in time (false: the timer fired, c is closed or
// being closed). A connection whose timer fired is never used again.
func closeAfter(c net.Conn, d time.Duration) func() bool {
	t := &connTimer{}
	time.AfterFunc(d, func() {
		t.mu.Lock()
		fire := !t.over
		t.over = true
		t.mu.Unlock()
		if fire {
			c.Close()
		}
	})
	return func() bool {
		t.mu.Lock()
		inTime := !t.over
		t.over = true
		t.mu.Unlock()
		return inTime
	}
}
