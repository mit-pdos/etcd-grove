package echo

import (
	"io"
	"net"
	"testing"
)

// TestCheckFires is the negative control of the client's check: against a
// server that corrupts its reply (it echoes the request with its first byte
// flipped), Call panics. The check is reached and can fail, so the robustness
// theorem's "no thread panics" excludes something.
func TestCheckFires(t *testing.T) {
	l, err := net.Listen("tcp", SrvAddr)
	if err != nil {
		t.Fatal(err)
	}
	defer l.Close()
	go func() {
		for {
			c, err := l.Accept()
			if err != nil {
				return
			}
			buf := make([]byte, reqLen)
			if _, err := io.ReadFull(c, buf); err == nil {
				buf[0] ^= 0xff
				c.Write(buf)
			}
			c.Close()
		}
	}()
	if !panics(Call) {
		t.Fatal("Call did not panic against a server that corrupts its reply")
	}
}

// panics reports whether f panics.
func panics(f func()) (p bool) {
	defer func() {
		if recover() != nil {
			p = true
		}
	}()
	f()
	return false
}
