package tcp

// Tests of the network layer's handling of network faults (findings N1-N4, C1 of the rabia-net
// verification, notes in the verification project's issues/): a fault of the network (a failed
// Accept, a connection that breaks, a write that fails) is an error the endpoint handles, as it
// already handles a failed read ("TCP connection closed"), not a panic of the process.

import (
	"bufio"
	"bytes"
	"encoding/binary"
	"errors"
	"net"
	"sync"
	"testing"
	"time"

	"rabia/internal/config"
	"rabia/internal/message"
)

var (
	confOnce  sync.Once
	resetAddr string // a listener that resets every connection it accepts (resetter)
)

// testConf sets the configuration once (routines of earlier tests may still run and read it).
func testConf() {
	confOnce.Do(func() {
		config.Conf.NServers = 2
		config.Conf.NFaulty = 0
		config.Conf.NClients = 6
		config.Conf.CalcConstants()
		resetAddr = resetter()
		config.Conf.Peers = []string{resetAddr, resetAddr}
	})
}

// noPanic runs f in a goroutine and fails the test if it panics within d; f may block.
func noPanic(t *testing.T, d time.Duration, f func()) {
	t.Helper()
	res := make(chan interface{}, 1)
	go func() {
		defer func() { res <- recover() }()
		f()
	}()
	select {
	case r := <-res:
		if r != nil {
			t.Fatalf("panic: %v", r)
		}
	case <-time.After(d):
	}
}

type failingWriter struct{}

func (failingWriter) Write(p []byte) (int, error) { return 0, errors.New("connection reset") }

// N3: a frame cut short (the connection broke in its middle) is a read error.
func TestBufReadShortFrame(t *testing.T) {
	var b bytes.Buffer
	var l [4]byte
	binary.LittleEndian.PutUint32(l[:], 10)
	b.Write(l[:])
	b.Write([]byte{1, 2, 3})
	noPanic(t, time.Second, func() {
		_, err := message.BufRead(bufio.NewReader(&b), make([]byte, 100))
		if err == nil {
			t.Errorf("BufRead of a cut frame: no error")
		}
	})
}

// N3: a write that fails is a write error.
func TestBufWriteFailedWrite(t *testing.T) {
	noPanic(t, time.Second, func() {
		w := bufio.NewWriterSize(failingWriter{}, 16)
		if err := message.BufWrite(w, make([]byte, 100)); err == nil {
			t.Errorf("BufWrite to a failing writer: no error")
		}
	})
}

// N1: the network layer's send routine ends when its connection breaks.
func TestNetSendHandlerBrokenConn(t *testing.T) {
	testConf()
	n := &NetTCP{Done: make(chan struct{}), Wg: &sync.WaitGroup{},
		SendChan: []chan []byte{make(chan []byte, 1)}, Writers: []*bufio.Writer{bufio.NewWriter(failingWriter{})}}
	n.SendChan[0] <- []byte{1, 2, 3}
	n.Wg.Add(1)
	noPanic(t, time.Second, func() { n.SendHandler(0) })
}

// N1: a failed Accept does not stop the server.
func TestNetAcceptFails(t *testing.T) {
	testConf()
	n := NetTCPInit(0, "127.0.0.1:0")
	_ = n.Listener.Close()
	noPanic(t, 500*time.Millisecond, func() { n.accepting() })
}

// N1: a connection that breaks before its handshake arrived is dropped.
func TestNetHandshakeCut(t *testing.T) {
	testConf()
	n := NetTCPInit(0, "127.0.0.1:0")
	defer n.Listener.Close()
	c, err := net.Dial("tcp", n.Listener.Addr().String())
	if err != nil {
		t.Fatal(err)
	}
	_ = c.Close()
	noPanic(t, 500*time.Millisecond, func() { n.accepting() })
}

// resetter accepts connections and resets each at once (SO_LINGER 0): a dialer's first write then
// may fail.
func resetter() string {
	l, err := net.Listen("tcp", "127.0.0.1:0")
	if err != nil {
		panic(err)
	}
	go func() {
		for {
			c, err := l.Accept()
			if err != nil {
				return
			}
			_ = c.(*net.TCPConn).SetLinger(0)
			_ = c.Close()
		}
	}()
	return l.Addr().String()
}

// N1: the network layer's handshake write may fail (the peer's connection reset); the server dials
// again, as after a failed dial. The reset races with the write, so the test tries many times.
func TestNetDialHandshakeWriteFails(t *testing.T) {
	testConf()
	for k := 0; k < 100; k++ {
		n := &NetTCP{Id: 0, SendChan: make([]chan []byte, 2), SendConn: make([]*net.Conn, 2),
			Writers: make([]*bufio.Writer, 2)}
		noPanic(t, 20*time.Millisecond, func() { n.dialing() })
	}
}

// N2: a socket option that fails (here: on a closed connection) does not stop the process.
func TestGetReaderWriterClosedConn(t *testing.T) {
	testConf()
	l, err := net.Listen("tcp", "127.0.0.1:0")
	if err != nil {
		t.Fatal(err)
	}
	defer l.Close()
	c, err := net.Dial("tcp", l.Addr().String())
	if err != nil {
		t.Fatal(err)
	}
	_ = c.Close()
	noPanic(t, time.Second, func() { GetReaderWriter(&c) })
}

// N4: a client connection that breaks before its handshake arrived is dropped by the proxy.
func TestProxyHandshakeCut(t *testing.T) {
	testConf()
	p := ProxyTcpInit(0, "127.0.0.1:0", make(chan message.Command, 1))
	defer p.Listener.Close()
	c, err := net.Dial("tcp", p.Listener.Addr().String())
	if err != nil {
		t.Fatal(err)
	}
	_ = c.Close()
	noPanic(t, 500*time.Millisecond, func() { p.connect() })
}

// C1: a client's send routine ends when its connection breaks.
func TestClientSendHandlerBrokenConn(t *testing.T) {
	testConf()
	c := ClientTcpInit(0, "127.0.0.1:1")
	c.Writer = bufio.NewWriter(failingWriter{})
	c.SendChan <- message.Command{CliId: 0, CliSeq: 1, Commands: []string{"1key00000"}}
	c.Wg.Add(1)
	noPanic(t, time.Second, func() { c.SendHandler() })
}

// C1: a client's handshake write may fail (the proxy's connection reset); the client dials again.
func TestClientHandshakeWriteFails(t *testing.T) {
	testConf()
	for k := 0; k < 100; k++ {
		c := ClientTcpInit(0, resetAddr)
		noPanic(t, 20*time.Millisecond, func() { c.connect() })
	}
}

// N5: a failed Listen (here: the address is in use for a while) does not stop the process; the endpoint listens once
// the address is free.
func TestListenFails(t *testing.T) {
	testConf()
	for _, init := range []func(string){
		func(a string) { ProxyTcpInit(0, a, make(chan message.Command, 1)).Listener.Close() },
		func(a string) { NetTCPInit(0, a).Listener.Close() },
	} {
		busy, err := net.Listen("tcp", "127.0.0.1:0")
		if err != nil {
			t.Fatal(err)
		}
		addr := busy.Addr().String()
		done := make(chan struct{})
		noPanic(t, 300*time.Millisecond, func() { init(addr); close(done) })
		busy.Close()
		select {
		case <-done:
		case <-time.After(2 * time.Second):
			t.Fatal("the endpoint did not listen once the address was free")
		}
	}
}

// N6: a frame longer than the reader's buffer (a client's put of a large value: the proxy reads requests into
// 400 KB) is a read error, not a panic.
func TestBufReadFrameTooLarge(t *testing.T) {
	var b bytes.Buffer
	var l [4]byte
	binary.LittleEndian.PutUint32(l[:], 1000)
	b.Write(l[:])
	b.Write(make([]byte, 1000))
	noPanic(t, time.Second, func() {
		if _, err := message.BufRead(bufio.NewReader(&b), make([]byte, 100)); err == nil {
			t.Errorf("BufRead of a frame longer than the buffer: no error")
		}
	})
}

// handshake dials addr and sends the handshake of id (a peer's or a client's).
func handshake(t *testing.T, addr string, id uint32) net.Conn {
	c, err := net.Dial("tcp", addr)
	if err != nil {
		t.Fatal(err)
	}
	data, _ := (&message.Command{CliId: id}).Marshal()
	if _, err := c.Write(append([]byte{byte(len(data)), 0, 0, 0}, data...)); err != nil {
		t.Fatal(err)
	}
	return c
}

// N7: a peer may deliver two whole handshakes (its first handshake write failed after its bytes were sent; it dials
// again): the network layer accepts each peer once, on its last connection; every peer gets a reader.
func TestNetDuplicateHandshake(t *testing.T) {
	testConf()
	n := NetTCPInit(0, "127.0.0.1:0")
	defer n.Listener.Close()
	a := n.Listener.Addr().String()
	done := make(chan struct{})
	go func() { n.accepting(); close(done) }()
	c1 := handshake(t, a, 0)
	time.Sleep(50 * time.Millisecond)
	c2 := handshake(t, a, 0)
	time.Sleep(50 * time.Millisecond)
	c3 := handshake(t, a, 1)
	defer c1.Close()
	defer c2.Close()
	defer c3.Close()
	<-done
	for id, r := range n.Readers {
		if r == nil {
			t.Fatalf("peer %d has no reader (a duplicate handshake was counted)", id)
		}
	}
}

// N7: a client that connects again is served on its new connection; its old connection is closed and its old
// routines do not touch the new one (go test -race).
func TestProxyDuplicateHandshake(t *testing.T) {
	testConf()
	in := make(chan message.Command, 10)
	p := ProxyTcpInit(0, "127.0.0.1:0", in)
	defer p.Listener.Close()
	p.Connect()
	a := p.Listener.Addr().String()
	c1 := handshake(t, a, 0)
	defer c1.Close()
	time.Sleep(50 * time.Millisecond)
	c2 := handshake(t, a, 0)
	defer c2.Close()
	time.Sleep(50 * time.Millisecond)
	data, _ := (&message.Command{CliId: 0, CliSeq: 7, Commands: []string{"1key00000"}}).Marshal()
	if _, err := c2.Write(append([]byte{byte(len(data)), 0, 0, 0}, data...)); err != nil {
		t.Fatal(err)
	}
	select {
	case r := <-in:
		if r.CliSeq != 7 {
			t.Fatalf("got %v", r)
		}
	case <-time.After(2 * time.Second):
		t.Fatal("the request on the new connection was not received")
	}
	// the old connection is closed by the proxy
	c1.SetReadDeadline(time.Now().Add(2 * time.Second))
	if _, err := c1.Read(make([]byte, 1)); err == nil {
		t.Fatal("the old connection is still open")
	}
}
