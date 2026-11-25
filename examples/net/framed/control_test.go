package framed

import (
	"io"
	"net"
	"testing"
)

// TestCheckFires is the negative control of the client's check: against a
// server whose reply to a message is one byte longer than the message (its
// payload with a byte appended, under a header one larger), Call panics at its
// first exchange. The check is reached and can fail, so the robustness
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
			for {
				hdr := make([]byte, 1)
				if _, err := io.ReadFull(c, hdr); err != nil {
					break
				}
				payload := make([]byte, int(hdr[0]))
				if _, err := io.ReadFull(c, payload); err != nil {
					break
				}
				n := byte(len(payload) + 1)
				reply := append([]byte{n}, append(payload, 0)[:n]...)
				if _, err := c.Write(reply); err != nil {
					break
				}
			}
			c.Close()
		}
	}()
	if !panics(Call) {
		t.Fatal("Call did not panic against a server that corrupts its replies")
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
