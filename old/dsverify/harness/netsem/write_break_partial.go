package netsem

import (
	"errors"
	"net"
	"time"
)

// WriteBreakPartial: a Write that a break stops returns the count the kernel took so far with
// the break's error, and the peer may have read some or all of those bytes. Here the peer reads
// part of a large Write, then closes abortively (SO_LINGER 0, a reset); the blocked Write
// returns k > 0 with ECONNRESET or EPIPE, and the bytes the peer read are among the k.
//
// Lean: Impl.lean, WriteOutcome (`code = errBroken`: the first `k` bytes appended to a live
// stream, then a break (`Conn.Breaks`), which keeps a prefix of the stream: all, some or none of
// them).
// Allowed: (k > 0, errBroken) with the peer having read up to k of the bytes.
// Excluded: the peer reading bytes past k; a reader reading bytes written after the break.
// Evidence: measured (below): 64 MiB to a peer that reads 1 MiB, then closes with SO_LINGER 0;
// the conformance probe (harness/conform, notes/conform.md F3) saw the same with the rig's reset
// fault over veth.
func WriteBreakPartial() (string, error) {
	d, a, err := pair()
	if err != nil {
		return "", err
	}
	defer d.Close()
	big := fill(64<<20, 'b')
	type res struct {
		k   int
		err error
	}
	ch := make(chan res, 1)
	go func() {
		k, e := d.Write(big)
		ch <- res{k, e}
	}()
	buf := make([]byte, 1<<16)
	read := 0
	a.SetReadDeadline(time.Now().Add(2 * time.Second))
	for read < 1<<20 {
		n, e := a.Read(buf)
		read += n
		if e != nil {
			break
		}
	}
	a.(*net.TCPConn).SetLinger(0)
	a.Close()
	r := <-ch
	s := sprintf("Write returned %d of %d with %s; the peer had read %d of its bytes, then closed abortively",
		r.k, len(big), describe(r.err), read)
	if r.err == nil || r.k < read {
		return "", errors.New("UNEXPECTED: " + s)
	}
	return s, nil
}
