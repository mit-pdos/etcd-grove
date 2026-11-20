package netsem

import (
	"net"
	"time"
)

// BreakSuffix and ResetThenEOF: a break (here a reset: the writer closes with SO_LINGER 0,
// as the kernel does for a connection it aborts) loses an arbitrary suffix of the bytes in
// flight: the reader gets a prefix of what was written, then an error (ECONNRESET), and then
// io.EOF on the next Read (Linux reports the reset once, then end of file).
//
// Lean: Impl.lean, Conn.Breaks (both streams cut, each keeping a prefix), BreakOrNot (a break at
// any Read, Write or Close of either end), StreamStatus.cut, ReadOutcome's last case
// (`s.status = .cut`: errBroken or errEOF).
// Allowed: any prefix, then an error or EOF, then EOF.
// Excluded: bytes after a gap; bytes never written.
// Evidence: measured (below: 8 MiB written to a peer that does not read, then an abortive
// close; the peer reads fewer bytes than were written, then ECONNRESET, then EOF). The
// break_netns_test.go variant makes the reset in the network (iptables REJECT tcp-reset in a
// network namespace).
func BreakSuffix() (string, error) {
	d, a, err := pair()
	if err != nil {
		return "", err
	}
	defer a.Close()
	big := fill(8<<20, 'y')
	d.SetWriteDeadline(time.Now().Add(200 * time.Millisecond))
	k, _ := d.Write(big)
	d.(*net.TCPConn).SetLinger(0)
	d.Close()
	time.Sleep(50 * time.Millisecond)
	got, errs := readAll(a, time.Second)
	return sprintf("wrote %d bytes; peer read %d, then %v", k, got, errs), nil
}
