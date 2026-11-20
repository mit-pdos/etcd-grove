package netsem

import "time"

// CloseThenEOF: after the peer's Close, a Read returns the bytes still unread, then io.EOF,
// and io.EOF again on every later Read. A Read on one's own closed end fails with "use of
// closed network connection" (errors.Is net.ErrClosed), not EOF.
//
// Lean: Impl.lean, StreamStatus.fin, CloseOutcome (the outgoing stream becomes fin),
// ReadOutcome's third case (`s.bytes = [] ∧ s.status = .fin ∧ code = errEOF`) and its first
// branch (`e.closed`: errClosed).
// Allowed: the remaining bytes, then EOF forever; errClosed on the closed end.
// Excluded: EOF before the remaining bytes; data after EOF.
// Evidence: measured (below); documented: io.EOF "returned by Read when no more input is
// available"; Go's conn.Read returns io.EOF unwrapped.
func CloseThenEOF() (string, error) {
	d, a, err := pair()
	if err != nil {
		return "", err
	}
	defer a.Close()
	d.Write([]byte("bye"))
	d.Close()
	time.Sleep(20 * time.Millisecond)
	got, errs := readAll(a, time.Second)
	buf := make([]byte, 4)
	_, eOwn := d.Read(buf)
	return sprintf("peer read %d bytes, then %v; Read on own closed end: %s",
		got, errs, describe(eOwn)), nil
}
