// Package wire holds the helpers the net examples share: reading a buffer in
// full from a net.Conn (io.ReadFull's loop, which grpc and net/http use to
// read frames and fixed-size headers), and blocking forever (the end of every
// node's boot program: a node's process never exits, see examples/net/README.md).
package wire

import "net"

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

// Forever blocks the calling goroutine forever.
func Forever() {
	select {}
}
