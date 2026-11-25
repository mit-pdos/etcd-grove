package duplex

import (
	"net"
	"testing"
)

// TestCheckFires is the negative control of the client's check: against a
// server that echoes each byte plus one, Call panics at the first byte it
// reads. The check is reached and can fail, so the robustness theorem's "no
// thread panics" excludes something.
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
				buf := make([]byte, 16)
				for {
					k, err := c.Read(buf)
					for i := 0; i < k; i++ {
						buf[i]++
					}
					if k > 0 {
						if _, err := c.Write(buf[:k]); err != nil {
							break
						}
					}
					if err != nil {
						break
					}
				}
				c.Close()
			}()
		}
	}()
	if !panics(Call) {
		t.Fatal("Call did not panic against a server that corrupts the bytes")
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
