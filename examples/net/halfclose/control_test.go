package halfclose

import (
	"io"
	"net"
	"testing"
)

// TestCheckFires is the negative control of the client's check: against a
// server whose response is not a prefix of the request (the request with its
// first byte flipped, or one byte for an empty request), Call panics. The
// check is reached and can fail, so the robustness theorem's "no thread
// panics" excludes something.
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
			req, err := io.ReadAll(c)
			if err == nil {
				if len(req) == 0 {
					req = []byte{0}
				} else {
					req[0] ^= 0xff
				}
				c.Write(req)
			}
			c.Close()
		}
	}()
	if !panics(Call) {
		t.Fatal("Call did not panic against a server whose response is not a prefix of the request")
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
