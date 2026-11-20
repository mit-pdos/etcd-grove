package netsem

import "time"

// ShortRead: a Read returns some of the next unread bytes, at least one and at most the
// buffer, in order; never more than was written, never out of order.
//
// Lean: Impl.lean, ReadOutcome's second case (`data ≠ [] ∧ data.length ≤ n ∧ data <+: s.bytes`).
// Allowed: fewer bytes than are buffered (a Read never waits to fill the buffer).
// Excluded: zero bytes with a nil error on a non-empty buffer; bytes out of order.
// Evidence: documented (io.Reader; Go's poll.FD.Read makes one read(2), which returns what is
// queued, at most len(p)); measured: two 5-byte writes 50 ms apart, then a Read with a
// 64-byte buffer returns 5, the next 5.
func ShortRead() (string, error) {
	d, a, err := pair()
	if err != nil {
		return "", err
	}
	defer d.Close()
	defer a.Close()
	d.Write([]byte("hello"))
	time.Sleep(50 * time.Millisecond)
	buf := make([]byte, 64)
	n1, _ := a.Read(buf)
	first := string(buf[:n1])
	d.Write([]byte("world"))
	time.Sleep(50 * time.Millisecond)
	small := make([]byte, 3)
	n2, _ := a.Read(small)
	n3, _ := a.Read(buf)
	return sprintf("read %d (%q), then with a 3-byte buffer %d (%q), then %d (%q)",
		n1, first, n2, small[:n2], n3, buf[:n3]), nil
}
