package netsem

import (
	"errors"
	"io"
	"net"
	"strings"
	"syscall"
	"time"
)

// ErrClosed: an operation on one's own closed end fails with an error for which
// errors.Is(err, net.ErrClosed) is true, and Timeout() and Temporary() are false: Read, Write,
// SetDeadline and a second Close on a closed connection; Accept and a second Close on a closed
// listener; and a Read or Accept that was blocked when another goroutine closed the conn or the
// listener. errors.Is(err, net.ErrClosed) is false for every error that comes from the network or
// the peer: io.EOF after the peer's Close, ECONNRESET after a reset, a deadline's timeout,
// ECONNREFUSED from Dial, EADDRINUSE from Listen. So a program can tell "I closed it" from "it
// failed" by errors.Is(err, net.ErrClosed), and nothing else.
//
// Lean: TrustedCode/net.lean, net.ErrClosed.init (one model-only pointer error, kept as the
// model's poll.ErrNetClosing and stored in net.ErrClosed) and net.model.codeErr (the Err of a
// closed-end error is that pointer, with Timeout()/Temporary() false; every other result code's
// Err is a fresh pointer, so errors.Is is true exactly for closed-end errors); Impl.lean,
// NetConn.errClosed (the result code of an operation on a closed end or listener).
// Allowed: errClosed on one's own closed end or listener, including for an operation blocked
// when the Close happened (a Write so stopped returns the count already written:
// WriteCloseRace).
// Excluded: errors.Is(err, net.ErrClosed) for an error the peer or the network caused; a
// closed-end error with Timeout() or Temporary() true.
// Evidence: measured (below); documented: net.ErrClosed "returned by an I/O call on a network
// connection that has already been closed, or that is closed by another goroutine before the
// I/O is completed"; Go's poll.FD returns ErrNetClosing (== net.ErrClosed) wrapped in an OpError.
func ErrClosed() (string, error) {
	var out []string
	bad := false
	note := func(name string, err error, wantClosed bool) {
		is := errors.Is(err, net.ErrClosed)
		s := sprintf("%s %v", name, is)
		var ne net.Error
		if is && errors.As(err, &ne) {
			s += sprintf(" (Timeout %v, Temporary %v)", ne.Timeout(), ne.Temporary())
		}
		if !is {
			s += " (" + shortErr(err) + ")"
		}
		if is != wantClosed {
			s += " UNEXPECTED: " + describe(err)
			bad = true
		}
		out = append(out, s)
	}

	// One's own closed connection.
	d, a, err := pair()
	if err != nil {
		return "", err
	}
	d.Close()
	_, e := d.Read(make([]byte, 4))
	note("Read", e, true)
	_, e = d.Write([]byte("x"))
	note("Write", e, true)
	note("SetDeadline", d.SetDeadline(time.Now()), true)
	note("Close again", d.Close(), true)

	// io.EOF at the peer of that Close.
	a.SetReadDeadline(time.Now().Add(time.Second))
	_, e = a.Read(make([]byte, 4))
	note("peer's EOF", e, false)
	a.Close()

	// A Read blocked when another goroutine closes the conn; before that, a deadline's timeout.
	d, a, err = pair()
	if err != nil {
		return "", err
	}
	d.SetReadDeadline(time.Now().Add(10 * time.Millisecond))
	_, e = d.Read(make([]byte, 4))
	note("timeout", e, false)
	ch := make(chan error, 1)
	go func() { _, e := a.Read(make([]byte, 4)); ch <- e }()
	time.Sleep(50 * time.Millisecond)
	a.Close()
	note("blocked Read", <-ch, true)
	d.Close()

	// ECONNRESET: the peer closes with SO_LINGER 0.
	d, a, err = pair()
	if err != nil {
		return "", err
	}
	d.(*net.TCPConn).SetLinger(0)
	d.Close()
	time.Sleep(20 * time.Millisecond)
	a.SetReadDeadline(time.Now().Add(time.Second))
	_, e = a.Read(make([]byte, 4))
	note("ECONNRESET", e, false)
	a.Close()

	// One's own closed listener, and an Accept blocked when it is closed.
	l, err := listen()
	if err != nil {
		return "", err
	}
	addr := l.Addr().String()
	_, e = listenAt(addr)
	note("EADDRINUSE", e, false)
	go func() { _, e := l.Accept(); ch <- e }()
	time.Sleep(50 * time.Millisecond)
	l.Close()
	note("blocked Accept", <-ch, true)
	_, e = l.Accept()
	note("Accept", e, true)
	note("listener Close again", l.Close(), true)
	_, e = dial(addr)
	note("ECONNREFUSED", e, false)

	res := "errors.Is(err, net.ErrClosed): " + strings.Join(out, "; ")
	if bad {
		return "", errors.New(res)
	}
	return res, nil
}

// shortErr names an error briefly: io.EOF, an errno, or a timeout.
func shortErr(err error) string {
	var errno syscall.Errno
	var ne net.Error
	switch {
	case err == nil:
		return "nil"
	case err == io.EOF:
		return "io.EOF"
	case errors.As(err, &errno):
		return errno.Error()
	case errors.As(err, &ne) && ne.Timeout():
		return "i/o timeout"
	}
	return err.Error()
}
