package netsem

import "time"

// PartialWrite: a Write appends a prefix of its buffer and returns its length; a short write
// comes with an error. With a write deadline set, a Write may time out after a prefix, and the
// peer then reads exactly that prefix. The same holds for the other errors that can stop a Write
// midway (WriteCloseRace, WriteBreakPartial).
//
// Lean: Impl.lean, WriteOutcome (`k ≤ data.length`; `code = errNone ∧ k = data.length`, or
// `errTimeout` with `writeDeadline`, or `errClosed`, or `errBroken` followed by a break; on a live
// stream the first `k` bytes appended, whatever the result).
// Allowed: (k < len, timeout) with the deadline set; the peer reading the k bytes.
// Excluded: k < len with a nil error (Go's poll.FD.Write loops until done or an error); bytes
// past k reaching the peer.
// Evidence: measured: 64 MiB to a peer that does not read, write deadline 200 ms: Write returns
// a short count with a timeout; the peer then reads exactly that many bytes. Documented: net.Conn
// "Write can be made to time out and return an error after a fixed time limit".
func PartialWrite() (string, error) {
	d, a, err := pair()
	if err != nil {
		return "", err
	}
	defer d.Close()
	defer a.Close()
	big := fill(64<<20, 'x')
	d.SetWriteDeadline(time.Now().Add(200 * time.Millisecond))
	k, werr := d.Write(big)
	d.Close() // the peer reads the prefix, then EOF
	got, errs := readAll(a, 2*time.Second)
	return sprintf("Write returned %d of %d with %s; peer read %d bytes, then %v",
		k, len(big), describe(werr), got, errs), nil
}
