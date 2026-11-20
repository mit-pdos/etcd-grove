package netsem

import (
	"errors"
	"fmt"
	"io"
	"net"
	"time"
)

// Where the examples put their ends. On loopback (the default) both ends are in this process's
// network namespace and the listener is on 127.0.0.1. veth_test.go points these at two of the
// rig's namespaces instead: the listener on 10.77.0.11 in node 1's, the dialer in node 0's.
var (
	listenHost = "127.0.0.1"
	inListenNS = func(f func()) { f() } // runs f where listeners are made
	inDialNS   = func(f func()) { f() } // runs f where dialers are made
)

// listenAt listens on addr where listeners are made.
func listenAt(addr string) (l net.Listener, err error) {
	inListenNS(func() { l, err = net.Listen("tcp", addr) })
	return l, err
}

// listen listens on a fresh port of listenHost.
func listen() (net.Listener, error) { return listenAt(listenHost + ":0") }

// dial dials addr from where dialers are made.
func dial(addr string) (c net.Conn, err error) {
	inDialNS(func() { c, err = net.Dial("tcp", addr) })
	return c, err
}

// pair returns the two ends of a fresh TCP connection: the dialer's and the acceptor's.
func pair() (dialer, acceptor net.Conn, err error) {
	l, err := listen()
	if err != nil {
		return nil, nil, err
	}
	defer l.Close()
	ch := make(chan net.Conn, 1)
	go func() {
		c, _ := l.Accept()
		ch <- c
	}()
	d, err := dial(l.Addr().String())
	if err != nil {
		return nil, nil, err
	}
	a := <-ch
	if a == nil {
		d.Close()
		return nil, nil, errors.New("accept failed")
	}
	return d, a, nil
}

// describe names an error as the model's result codes do.
func describe(err error) string {
	if err == nil {
		return "nil"
	}
	if err == io.EOF {
		return "EOF"
	}
	var ne net.Error
	if errors.As(err, &ne) && ne.Timeout() {
		return "timeout(" + err.Error() + ")"
	}
	if errors.Is(err, net.ErrClosed) {
		return "closed(" + err.Error() + ")"
	}
	return "error(" + err.Error() + ")"
}

// readAll reads until an error or until the deadline d passes with nothing more to read,
// and returns the bytes read and the sequence of errors seen (up to two after the first).
func readAll(c net.Conn, d time.Duration) (int, []string) {
	buf := make([]byte, 1<<16)
	total := 0
	var errs []string
	for len(errs) < 3 {
		c.SetReadDeadline(time.Now().Add(d))
		n, err := c.Read(buf)
		total += n
		if err != nil {
			errs = append(errs, describe(err))
			var ne net.Error
			if errors.As(err, &ne) && ne.Timeout() {
				break
			}
		}
	}
	return total, errs
}

func fill(n int, b byte) []byte {
	p := make([]byte, n)
	for i := range p {
		p[i] = b
	}
	return p
}

func sprintf(format string, a ...any) string { return fmt.Sprintf(format, a...) }
