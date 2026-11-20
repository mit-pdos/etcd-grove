package netsem

// ZeroRead: a Read with an empty buffer returns (0, nil) without looking at the connection,
// even after the peer closed (but not on one's own closed end).
//
// Lean: Impl.lean, ReadOutcome's second branch (`n = 0`: `errNone`).
// Evidence: measured (below); documented: poll.FD.Read returns at once for len(p) == 0, after
// the closed check.
func ZeroRead() (string, error) {
	d, a, err := pair()
	if err != nil {
		return "", err
	}
	defer a.Close()
	d.Close()
	n, e := a.Read(nil)
	return sprintf("Read(nil) after the peer's Close: %d %s", n, describe(e)), nil
}
