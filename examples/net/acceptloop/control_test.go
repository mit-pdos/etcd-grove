package acceptloop

import (
	"io"
	"net"
	"testing"
)

// TestCheckFires is the negative control of each call's check: against a
// server that replies with another id (the request plus one), CallOne panics.
// The check is reached and can fail, so the robustness theorem's "no thread
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
			go func() {
				buf := make([]byte, 1)
				if _, err := io.ReadFull(c, buf); err == nil {
					buf[0]++
					c.Write(buf)
				}
				c.Close()
			}()
		}
	}()
	if !panics(func() { CallOne(1) }) {
		t.Fatal("CallOne did not panic against a server that replies with another id")
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
