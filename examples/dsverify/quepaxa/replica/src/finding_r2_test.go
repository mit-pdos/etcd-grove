package raxos

import (
	"encoding/binary"
	"net"
	"strings"
	"testing"
	"time"
)

func portOf(a net.Addr) string {
	s := a.String()
	return s[strings.LastIndex(s, ":")+1:]
}

// TestR2ProxyNetworkFaults (finding R2): the proxy's accept routine must survive the network's
// faults: a proxy port it cannot listen on yet (taken), and a client connection that breaks
// before its handshake arrived; a client that connects afterwards is dialed back.
func TestR2ProxyNetworkFaults(t *testing.T) {
	taken, err := net.Listen("tcp", "0.0.0.0:0") // the proxy's port, taken at first
	if err != nil {
		t.Fatal(err)
	}
	cl, err := net.Listen("tcp", "127.0.0.1:0") // the client's listener for connections back
	if err != nil {
		t.Fatal(err)
	}
	defer cl.Close()
	cfg := testConfig()
	cfg.Peers[1].PROXYPORT = portOf(taken.Addr())
	cfg.Clients[0].CLIENTPORT = portOf(cl.Addr())
	pr := NewProxy(2, cfg, nil, nil, nil, "/tmp/", 50, 1, 20000, false, 0, nil, 1, &ClientBatchStore{}, 0,
		nil, nil, 0, 5, nil, 0, 8, 8, 0)
	go pr.waitForConnections()
	time.Sleep(200 * time.Millisecond)
	taken.Close()
	addr := "127.0.0.1:" + portOf(taken.Addr())
	// a connection that breaks before its handshake
	var c net.Conn
	for i := 0; ; i++ {
		c, err = net.Dial("tcp", addr)
		if err == nil {
			break
		}
		if i == 50 {
			t.Fatalf("the proxy does not listen: %v", err)
		}
		time.Sleep(100 * time.Millisecond)
	}
	c.Write([]byte{21})
	c.Close()
	// a client that connects with its handshake is dialed back
	c, err = net.Dial("tcp", addr)
	if err != nil {
		t.Fatal(err)
	}
	defer c.Close()
	var hs [4]byte
	binary.LittleEndian.PutUint16(hs[:], 21)
	c.Write(hs[:])
	back, err := cl.Accept()
	if err != nil {
		t.Fatal(err)
	}
	defer back.Close()
	back.SetReadDeadline(time.Now().Add(5 * time.Second))
	if _, err := back.Read(hs[:]); err != nil || binary.LittleEndian.Uint16(hs[:]) != 2 {
		t.Fatalf("connection back: %v %v", hs, err)
	}
}
