//go:build !rpcmodel

// (The model build needs the kit's codec, registered by examples/quepaxanet, to marshal an answer.)

package raxos

import (
	"io"
	"net"
	"sync"
	"testing"
)

// clientListener accepts the proxy's connections back and reports, for each, its first 4 bytes.
func clientListener(t *testing.T) (net.Listener, chan [4]byte) {
	l, err := net.Listen("tcp", "127.0.0.1:0")
	if err != nil {
		t.Fatal(err)
	}
	firsts := make(chan [4]byte, 100000)
	go func() {
		for {
			c, err := l.Accept()
			if err != nil {
				return
			}
			go func() {
				var hs [4]byte
				if _, err := io.ReadFull(c, hs[:]); err == nil {
					firsts <- hs
				}
				io.Copy(io.Discard, c)
			}()
		}
	}()
	return l, firsts
}

// TestP1ConnectionBackWhileAnswering (finding P1): the accept routine dials a client back (a
// client that reconnects is dialed back again) while the sender goroutines answer it: the
// writers' map is written and read without synchronization (Go's "concurrent map read and map
// write" when they coincide; under -race, a data race).
func TestP1ConnectionBackWhileAnswering(t *testing.T) {
	l, _ := clientListener(t)
	defer l.Close()
	cfg := testConfig()
	cfg.Clients[0].CLIENTPORT = portOf(l.Addr())
	pr := NewProxy(2, cfg, nil, nil, nil, "/tmp/", 50, 1, 20000, false, 0, nil, 1, &ClientBatchStore{}, 0,
		nil, nil, 0, 5, nil, 0, 8, 8, 0)
	pr.connectToClient(21)
	var wg sync.WaitGroup
	stop := make(chan bool)
	wg.Add(1)
	go func() {
		defer wg.Done()
		for {
			select {
			case <-stop:
				return
			default:
				pr.internalSendMessage(21, answer())
			}
		}
	}()
	const n = 300
	for i := 0; i < n; i++ {
		pr.connectToClient(21) // the client reconnected: the proxy dials it back
	}
	close(stop)
	wg.Wait()
}
