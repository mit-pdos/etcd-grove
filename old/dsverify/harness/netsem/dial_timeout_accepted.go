package netsem

import (
	"errors"
	"net"
	"sync"
	"time"
)

// DialTimeoutAccepted: a Dial that fails can still have made a connection that the listener's
// Accept returns. Go's connect waits for the socket to become writable under the dial's
// deadline; when the deadline fires, Go closes the socket and returns "i/o timeout", even if the
// kernel has finished the handshake meanwhile. The listener's kernel has then queued the
// connection, and Accept returns it. Its acceptor reads io.EOF (Go's close sent a FIN; nothing
// was written) or, after a reset, an error; never data.
//
// Lean: Impl.lean, NetConnStep "Dial" (its third case: a failure that leaves Conn.abandoned
// pending at an open listener on the address: the dialer's end closed, its stream fin and empty)
// and TrustedCode/net.lean, DialTimeout.impl (Dial).
// Allowed: Dial (DialTimeout) failing while its connection is accepted; the acceptor reading
// io.EOF or an error.
// Excluded: such a connection carrying data; a failed Dial leaving a connection with no listener
// open on the address.
// Evidence: measured (below): DialTimeout with timeouts of 1 to 60 us on loopback, the acceptor
// reading one byte of each connection (the dialer writes one byte when its Dial succeeds); the
// conformance probe (harness/conform, notes/conform.md F1) saw the same over veth with netem
// delay.
func DialTimeoutAccepted() (string, error) {
	l, err := listen()
	if err != nil {
		return "", err
	}
	addr := l.Addr().String()
	var mu sync.Mutex
	got := map[string]int{}
	var wg sync.WaitGroup
	done := make(chan struct{})
	go func() {
		defer close(done)
		for {
			c, err := l.Accept()
			if err != nil {
				return
			}
			wg.Add(1)
			go func() {
				defer wg.Done()
				defer c.Close()
				b := make([]byte, 2)
				c.SetReadDeadline(time.Now().Add(2 * time.Second))
				n, err := c.Read(b)
				k := "data " + string(b[:n])
				if n == 0 {
					k = describeShort(err)
				}
				mu.Lock()
				got[k]++
				mu.Unlock()
			}()
		}
	}()
	const dials = 5000
	ok, fail := 0, 0
	for i := 0; i < dials; i++ {
		to := time.Duration(1+i%60) * time.Microsecond
		var c net.Conn
		inDialNS(func() { c, err = net.DialTimeout("tcp", addr, to) })
		if err != nil {
			fail++
			continue
		}
		ok++
		c.Write([]byte{'D'})
		c.Close()
	}
	time.Sleep(200 * time.Millisecond)
	l.Close()
	<-done
	wg.Wait()
	accepted := 0
	for _, v := range got {
		accepted += v
	}
	res := sprintf("%d DialTimeouts (1..60 us): %d ok, %d failed; %d accepted: %v; accepted from a failed Dial: %d",
		dials, ok, fail, accepted, got, accepted-ok)
	for k := range got {
		if len(k) > 4 && k[:5] == "data " && k != "data D" {
			return "", errors.New("UNEXPECTED (data the dialers did not write): " + res)
		}
	}
	if got["data D"] != ok {
		// a connection of a failed Dial carried data, or a successful Dial's byte was lost
		return "", errors.New("UNEXPECTED (accepted with data != successful Dials): " + res)
	}
	return res, nil
}

// describeShort is describe without the error's text.
func describeShort(err error) string {
	d := describe(err)
	for i := 0; i < len(d); i++ {
		if d[i] == '(' {
			if d[:i] == "error" {
				return "error(" + shortErr(err) + ")"
			}
			return d[:i]
		}
	}
	return d
}
