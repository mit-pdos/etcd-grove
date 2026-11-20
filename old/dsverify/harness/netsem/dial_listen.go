package netsem

import "time"

// DialRefused, ListenInUse, ListenerClosePending: Dial to an address with no listener fails;
// Listen on an address with an open listener fails; a connection dialed but not yet accepted
// when its listener closes is reset (its dialer sees an error).
//
// Lean: Impl.lean, NetConnStep "Dial" (a fresh connection only if a listener is open on the
// address string; failure always allowed), "Listen" (success only if no open listener has the
// address string; failure always allowed), "CloseListener" (pending connections dropped; their
// dialer end then sees a break through BreakOrNot).
// Allowed: Dial failing even with a listener (backlog full, handshake timeout), and then possibly
// leaving a connection that Accept returns (DialTimeoutAccepted); Listen failing.
// Excluded: Dial succeeding with no listener; two open listeners on one address.
// Evidence: measured (below); Dial's success to a listener that never accepts is documented
// (listen(2): the backlog completes handshakes without accept).
func DialListen() (string, error) {
	l, err := listen()
	if err != nil {
		return "", err
	}
	addr := l.Addr().String()
	_, eDup := listenAt(addr)
	c, eDial := dial(addr) // not accepted
	l.Close()
	time.Sleep(20 * time.Millisecond)
	var ePending string
	if c != nil {
		buf := make([]byte, 1)
		c.SetReadDeadline(time.Now().Add(time.Second))
		_, e := c.Read(buf)
		ePending = describe(e)
		c.Close()
	}
	_, eRefused := dial(addr)
	return sprintf("second Listen: %s; Dial with no Accept: %s, then its Read after the listener's Close: %s; Dial after Close: %s",
		describe(eDup), describe(eDial), ePending, describe(eRefused)), nil
}
