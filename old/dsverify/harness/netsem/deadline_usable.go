package netsem

import "time"

// DeadlineUsable: with a deadline set, any Read or Write may time out (Timeout() true); the
// connection stays usable: after the deadline is cleared, the next Read returns the data. A
// deadline in the past times out even with data buffered.
//
// Lean: Impl.lean, EndState.readDeadline/writeDeadline, ReadOutcome's first case
// (`e.readDeadline ∧ code = errTimeout ∧ c' = c`), DeadlineOutcome; TrustedCode/net.lean
// model.setDeadline (set unless the zero time.Time), model.codeErr (timeout: Timeout() and
// Temporary() true).
// Allowed: a timeout, then success on the same connection.
// Excluded: a timeout with no deadline set; a timeout that changes the stream.
// Evidence: measured (below); documented: net.Conn "a deadline ... can be extended by calling
// SetDeadline again"; os.ErrDeadlineExceeded's Timeout() is true.
func DeadlineUsable() (string, error) {
	d, a, err := pair()
	if err != nil {
		return "", err
	}
	defer d.Close()
	defer a.Close()
	buf := make([]byte, 16)
	a.SetReadDeadline(time.Now().Add(50 * time.Millisecond))
	_, e1 := a.Read(buf)
	d.Write([]byte("late"))
	time.Sleep(20 * time.Millisecond)
	a.SetReadDeadline(time.Now().Add(-time.Second)) // in the past, data buffered
	_, e2 := a.Read(buf)
	a.SetReadDeadline(time.Time{}) // cleared
	n, e3 := a.Read(buf)
	return sprintf("first Read: %s; with data buffered and a past deadline: %s; after clearing: %d %q %s",
		describe(e1), describe(e2), n, buf[:n], describe(e3)), nil
}
