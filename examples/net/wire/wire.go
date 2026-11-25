// Package wire holds the helpers the net examples share: reading a buffer in
// full from a net.Conn (io.ReadFull's loop, which grpc and net/http use to
// read frames and fixed-size headers), and drawing the clients' payloads and
// counts at random (Goose's primitive.RandomUint64), so that a check covers
// every input up to the example's caps, not one fixed workload.
package wire

import (
	"net"

	"github.com/goose-lang/primitive"
)

// RandomInt returns a number drawn at random in [0, max]; max must be in
// [0, 2^31).
func RandomInt(max int) int {
	return int(primitive.RandomUint64() % uint64(max+1))
}

// RandomBytes returns a new slice of n bytes, each drawn at random; n must be
// non-negative.
func RandomBytes(n int) []byte {
	b := make([]byte, n)
	for i := 0; i < n; i++ {
		b[i] = byte(primitive.RandomUint64())
	}
	return b
}

// ReadFull reads exactly len(buf) bytes from c into buf, as io.ReadFull does:
// it loops over c.Read, which may return fewer bytes than asked. It returns
// false on any error before buf is full (an EOF included).
func ReadFull(c net.Conn, buf []byte) bool {
	n := 0
	for n < len(buf) {
		k, err := c.Read(buf[n:])
		n += k
		if err != nil {
			return n == len(buf)
		}
	}
	return true
}
