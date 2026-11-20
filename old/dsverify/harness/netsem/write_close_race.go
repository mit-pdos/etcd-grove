package netsem

import "time"

// WriteCloseRace: a Write blocked for buffer space when another goroutine Closes the same end
// returns the count the kernel took so far with net.ErrClosed, and the peer reads exactly those
// bytes, then io.EOF. Go's poll.FD.Write loops over write(2); woken by the Close, it returns the
// bytes written so far with ErrNetClosing. The socket itself is closed (a FIN after the bytes)
// when the Write releases it.
//
// Lean: Impl.lean, WriteOutcome (on an open end, `code = errClosed` with the first `k` bytes
// appended to a live stream: the model's Write is one step, linearized before that Close, which
// it cannot see, so any Write at an open end may fail so; an over-approximation).
// Allowed: (k > 0, errClosed) with the end open when the Write began, the peer reading the k bytes.
// Excluded: bytes past k reaching the peer; (k > 0, errClosed) on an end closed before the Write
// (the Write then fails at once with k = 0).
// Evidence: measured (below): 64 MiB to a peer that does not read yet, the writer's Close after
// 100 ms; the conformance probe (harness/conform, notes/conform.md F2) saw the same over veth.
func WriteCloseRace() (string, error) {
	d, a, err := pair()
	if err != nil {
		return "", err
	}
	defer a.Close()
	big := fill(64<<20, 'w')
	go func() {
		time.Sleep(100 * time.Millisecond)
		d.Close()
	}()
	k, werr := d.Write(big)
	got, errs := readAll(a, 2*time.Second)
	return sprintf("Write returned %d of %d with %s; peer read %d bytes, then %v",
		k, len(big), describe(werr), got, errs), nil
}
