//go:build !rpcmodel

// (The model build needs the kit's codec, registered by examples/quepaxanet, to marshal an answer.)

package raxos

import (
	"encoding/binary"
	"sync"
	"testing"
)

// TestP3HandshakeFirst (finding P3): every connection back to a client starts with the proxy's
// handshake (its name), which the client reads first; the new writer must not be visible to the
// sender goroutines before the handshake is written, or an answer can reach the client ahead of
// it. The window is small: run with -race (its scheduling shows it), or many times.
func TestP3HandshakeFirst(t *testing.T) {
	for trial := 0; trial < 40; trial++ {
		handshakeFirst(t)
	}
}

func handshakeFirst(t *testing.T) {
	l, firsts := clientListener(t)
	defer l.Close()
	cfg := testConfig()
	cfg.Clients[0].CLIENTPORT = portOf(l.Addr())
	pr := NewProxy(2, cfg, nil, nil, nil, "/tmp/", 50, 1, 20000, false, 0, nil, 1, &ClientBatchStore{}, 0,
		nil, nil, 0, 5, nil, 0, 8, 8, 0)
	pr.connectToClient(21)
	var wg sync.WaitGroup
	stop := make(chan bool)
	for k := 0; k < 32; k++ { // QuePaxa's proxy has 200 sender goroutines
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
	}
	const n = 500
	for i := 0; i < n; i++ {
		pr.connectToClient(21) // the client reconnected: the proxy dials it back
	}
	close(stop)
	wg.Wait()
	for i := 0; i < n+1; i++ {
		hs := <-firsts
		if binary.LittleEndian.Uint16(hs[:]) != 2 || hs[2] != 0 || hs[3] != 0 {
			t.Fatalf("a connection back starts with %v, not the proxy's handshake", hs)
		}
	}
}
