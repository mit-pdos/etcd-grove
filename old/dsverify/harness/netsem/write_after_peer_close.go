package netsem

import "time"

// WriteAfterPeerClose: after the peer closed, a Write may still succeed (the kernel accepts the
// bytes; the peer's kernel answers with a reset and the bytes are lost), and a later Write fails
// (EPIPE or ECONNRESET).
//
// Lean: Impl.lean, WriteOutcome on a stream that is not live (bytes discarded; success or
// errBroken), reached through a break (the peer's Close with unread data, or the reset its
// kernel sends, is a break at the writer's operation).
// Allowed: success, then an error; the bytes never read.
// Excluded: the bytes of a Write made after the break reaching a reader. (A Write that the break
// stops midway is WriteBreakPartial: the bytes the kernel took before it may be read.)
// Evidence: measured (below).
func WriteAfterPeerClose() (string, error) {
	d, a, err := pair()
	if err != nil {
		return "", err
	}
	defer d.Close()
	a.Close()
	time.Sleep(20 * time.Millisecond)
	_, e1 := d.Write([]byte("one"))
	time.Sleep(20 * time.Millisecond)
	_, e2 := d.Write([]byte("two"))
	_, e3 := d.Write([]byte("three"))
	return sprintf("Writes after the peer's Close: %s, %s, %s", describe(e1), describe(e2), describe(e3)), nil
}
