package paxos

import (
	"net"
	"time"

	"github.com/tchajed/marshal"
)

// The network interface over Go's net package: each node of a deployment
// (one process) listens on one TCP address and hosts some agents; every agent
// knows the address of the node of every other agent. Agent a sends to agent b
// over a connection that a dials to b's node and uses for nothing else (one
// connection per ordered pair of agents; the receiving node only reads it). A
// message travels as one frame: its length as an 8-byte little-endian word,
// then marshalMessage's encoding. The receiving node reads frames from every
// connection it accepts and puts each message in the inbox of the agent it is
// addressed to; recv takes from the agent's inbox, with a timeout.
//
// Any error ends a connection: a send that fails closes it and dials a fresh
// one, once; a reader that fails closes its end. A message may be lost
// (a failed dial or write, a break, a full inbox), never reordered within a
// connection, duplicated or corrupted (TCP). Every blocking operation has a
// bound: dials (DialTimeoutMs), writes (WriteTimeoutMs) and reads
// (IdleTimeoutMs), so a partition does not stall a node for TCP's minutes.

// DialTimeoutMs bounds a dial.
const DialTimeoutMs uint64 = 500

// WriteTimeoutMs bounds the write of one frame.
const WriteTimeoutMs uint64 = 1000

// IdleTimeoutMs is how long a reader waits for the next frame before it
// closes the connection (its sender redials when it next sends).
const IdleTimeoutMs uint64 = 30000

// InboxSize is the capacity of an agent's inbox; a message to a full inbox is
// dropped.
const InboxSize uint64 = 1024

// MaxFrame bounds the length of a frame's body.
const MaxFrame uint64 = 1 << 20

// msgHeader is the length of marshalMessage's encoding of a message with an
// empty value: five integers and the value's length.
const msgHeader uint64 = 48

// tcpNode is the network state of one node: the addresses of every agent's
// node, and the inboxes of this node's agents. Both maps are read-only once the
// node is made.
type tcpNode struct {
	addrs map[int]string
	inbox map[int]chan message
}

// newTCPNode makes the network state of a node that hosts the agents local;
// addrs maps every agent to the address of its node.
func newTCPNode(addrs map[int]string, local []int) *tcpNode {
	inbox := make(map[int]chan message)
	for _, id := range local {
		inbox[id] = make(chan message, InboxSize)
	}
	return &tcpNode{addrs: addrs, inbox: inbox}
}

// serve listens on addr and accepts connections in a new goroutine. It tries
// up to tries times, 100 ms apart, and reports whether it listens.
func (nd *tcpNode) serve(addr string, tries uint64) bool {
	for i := uint64(0); i < tries; i++ {
		l, err := net.Listen("tcp", addr)
		if err == nil {
			go nd.acceptLoop(l)
			return true
		}
		time.Sleep(100 * time.Millisecond)
	}
	return false
}

// acceptLoop accepts connections forever, reading each in a new goroutine.
func (nd *tcpNode) acceptLoop(l net.Listener) {
	for {
		c, err := l.Accept()
		if err != nil {
			time.Sleep(10 * time.Millisecond)
			continue
		}
		go nd.readLoop(c)
	}
}

// readLoop delivers the messages framed on c until a read fails, times out
// (IdleTimeoutMs without a frame) or a frame is malformed, then closes c.
func (nd *tcpNode) readLoop(c net.Conn) {
	for {
		c.SetReadDeadline(time.Now().Add(time.Duration(IdleTimeoutMs) * time.Millisecond))
		b, ok := readFrame(c)
		if !ok {
			break
		}
		nd.deliver(unmarshalMessage(b))
	}
	c.Close()
}

// deliver puts m in the inbox of agent m.to; it drops m if m.to is not an
// agent of this node or its inbox is full.
func (nd *tcpNode) deliver(m message) {
	q, ok := nd.inbox[m.to]
	if !ok {
		return
	}
	select {
	case q <- m:
	default:
	}
}

// readFull reads exactly len(buf) bytes from c into buf, or reports failure.
func readFull(c net.Conn, buf []byte) bool {
	n := 0
	for n < len(buf) {
		k, err := c.Read(buf[n:])
		if err != nil {
			return false
		}
		n += k
	}
	return true
}

// readFrame reads the next frame from c and returns its body, a well-formed
// encoding of a message; false if a read fails or the frame is malformed.
func readFrame(c net.Conn) ([]byte, bool) {
	hdr := make([]byte, 8)
	if !readFull(c, hdr) {
		return nil, false
	}
	n, _ := marshal.ReadInt(hdr)
	if n < msgHeader || n > MaxFrame {
		return nil, false
	}
	b := make([]byte, n)
	if !readFull(c, b) {
		return nil, false
	}
	vlen, _ := marshal.ReadInt(b[40:])
	if vlen != n-msgHeader {
		return nil, false
	}
	return b, true
}

// encodeFrame is m's frame: the length of m's encoding, then the encoding.
func encodeFrame(m message) []byte {
	body := marshalMessage(m)
	b := make([]byte, 0, 8+len(body))
	b = marshal.WriteInt(b, uint64(len(body)))
	return marshal.WriteBytes(b, body)
}

// writeFrame writes f to c within WriteTimeoutMs; false on any error (some
// prefix of f may have been sent, so c must not be used again).
func writeFrame(c net.Conn, f []byte) bool {
	c.SetWriteDeadline(time.Now().Add(time.Duration(WriteTimeoutMs) * time.Millisecond))
	_, err := c.Write(f)
	return err == nil
}

// tcpNetwork is agent me's network (the network interface): its node, and the
// connections it has dialed, by destination agent. send uses conns and recv the
// inbox only, so one goroutine may send while another receives; sends must not
// be concurrent.
type tcpNetwork struct {
	node  *tcpNode
	me    int
	conns map[int]net.Conn
}

// network is agent id's network on this node.
func (nd *tcpNode) network(id int) *tcpNetwork {
	return &tcpNetwork{node: nd, me: id, conns: make(map[int]net.Conn)}
}

// send sends m to agent m.to: over the connection to m.to if there is one;
// if there is none, or the write fails, over a newly dialed connection. The
// message is dropped if m.to is unknown or the dial or the new write fails.
func (nt *tcpNetwork) send(m message) {
	f := encodeFrame(m)
	c, ok := nt.conns[m.to]
	if ok {
		if writeFrame(c, f) {
			return
		}
		c.Close()
		delete(nt.conns, m.to)
	}
	addr, known := nt.node.addrs[m.to]
	if !known {
		return
	}
	c2, err := net.DialTimeout("tcp", addr, time.Duration(DialTimeoutMs)*time.Millisecond)
	if err != nil {
		return
	}
	if !writeFrame(c2, f) {
		c2.Close()
		return
	}
	nt.conns[m.to] = c2
}

// recv waits at most timeout for a message to agent me.
func (nt *tcpNetwork) recv(timeout time.Duration) (message, bool) {
	select {
	case m := <-nt.node.inbox[nt.me]:
		return m, true
	case <-time.After(timeout):
		return message{}, false
	}
}

// poll takes a message to agent me if one is waiting, without blocking.
func (nt *tcpNetwork) poll() (message, bool) {
	select {
	case m := <-nt.node.inbox[nt.me]:
		return m, true
	default:
		return message{}, false
	}
}
