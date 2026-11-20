package netsem

import "time"

// CloseUnreadResets: a Close with unread incoming bytes resets the connection: the peer may get
// ECONNRESET instead of EOF, and may lose bytes the closer had written.
//
// Lean: Impl.lean, CloseOutcome (unread incoming bytes are dropped with the end) together with
// BreakOrNot (the reset is a break at the peer's next operation).
// Allowed: the closer's bytes then EOF; a prefix then ECONNRESET.
// Evidence: measured (below).
func CloseUnreadResets() (string, error) {
	d, a, err := pair()
	if err != nil {
		return "", err
	}
	defer d.Close()
	d.Write([]byte("unread by the acceptor"))
	time.Sleep(20 * time.Millisecond)
	a.Write([]byte("from the acceptor"))
	a.Close()
	time.Sleep(50 * time.Millisecond)
	got, errs := readAll(d, time.Second)
	return sprintf("dialer read %d bytes, then %v", got, errs), nil
}
