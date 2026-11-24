package kvnet

import (
	"net"
	"time"

	"go.etcd.io/raft/v3"
	pb "go.etcd.io/raft/v3/raftpb"
)

// queueLen bounds the messages waiting for a peer's connection: one more is dropped (raft
// retransmits).
const queueLen = 256

// dialTimeout bounds a dial, and writeTimeout a frame's write: a peer that takes longer is
// unreachable for now, and the message is dropped.
const (
	dialTimeout  = 50 * time.Millisecond
	writeTimeout = 200 * time.Millisecond
)

// stepTimeout bounds how long the receiver waits for the node to take a message, as kvdurable's
// network does (Step of a forwarded proposal blocks while the node knows no leader).
const stepTimeout = 5 * time.Millisecond

// peer is the sending side of the connection to one peer: the messages waiting, which its
// goroutine (peer.run) writes in order to one connection, dialed when needed.
type peer struct {
	id    uint64
	addr  string
	queue chan *pb.Message
}

// Transport sends a node's messages to its peers, each over a TCP connection of its own (helloPeer),
// and hands the messages its listener receives to the node. A message is sent at most once,
// never retried: raft retransmits what matters. It makes no fault of its own: the network's are
// the environment's (examples/lib/robust). The node learns
// of a message dropped (ReportUnreachable) and of each snapshot's fate (ReportSnapshot, after its
// frame is written or dropped).
type Transport struct {
	id    uint64
	node  raft.Node
	stats *Stats
	peers map[uint64]*peer // every other replica the program knows, read-only once started
	stopc chan struct{}    // closed by stop: the senders return
}

// peerTransport carries an incarnation's raft messages to its peers: this file's, over TCP
// (Transport), or UDP's. Node.restart stops one and starts the next incarnation's with the same
// constructor (newPeerTransport); what a transport receives it steps on the current incarnation's
// node (Node.stepPeer).
type peerTransport interface {
	// start starts it once the incarnation's node exists.
	start(node raft.Node)
	// Send hands it the node's messages, without waiting.
	Send(ms []*pb.Message)
	// stop ends it once the incarnation's node is stopped.
	stop()
}

// newPeerTransport makes the transport of node id, whose peers' addresses are addrs (by id; its
// own included), counting in stats.
type newPeerTransport func(id uint64, addrs map[uint64]string, stats *Stats) peerTransport

// newTCPTransport is the TCP transport (newTransport), as a newPeerTransport.
func newTCPTransport(id uint64, addrs map[uint64]string, stats *Stats) peerTransport {
	return newTransport(id, addrs, stats)
}

// newTransport is the transport of node id, whose peers' addresses are addrs (by id; its own
// included, and left out: raft never sends to itself).
func newTransport(id uint64, addrs map[uint64]string, stats *Stats) *Transport {
	t := &Transport{id: id, stats: stats, peers: make(map[uint64]*peer), stopc: make(chan struct{})}
	for pid, addr := range addrs {
		if pid != id {
			t.peers[pid] = &peer{id: pid, addr: addr, queue: make(chan *pb.Message, queueLen)}
		}
	}
	return t
}

// start starts the senders, a goroutine per peer, once the node exists.
func (t *Transport) start(node raft.Node) {
	t.node = node
	for _, p := range t.peers {
		go t.runPeer(p)
	}
}

// stop ends the senders (the incarnation's node is stopped: Replica.stop): each closes its
// connection and returns, leaving what its queue still holds unsent (the next incarnation's
// transport has queues of its own).
func (t *Transport) stop() {
	close(t.stopc)
}

// Send hands each of ms to its peer's sender, without waiting; one to an unknown peer, or one
// whose peer's queue is full, is dropped.
func (t *Transport) Send(ms []*pb.Message) {
	for _, m := range ms {
		p, ok := t.peers[m.GetTo()]
		if !ok {
			t.dropped(m)
			continue
		}
		t.enqueue(p, m)
	}
}

// enqueue queues m for p, or drops it if p's queue is full.
func (t *Transport) enqueue(p *peer, m *pb.Message) {
	select {
	case p.queue <- m:
	default:
		t.dropped(m)
	}
}

// dropped tells the node that m was not sent.
func (t *Transport) dropped(m *pb.Message) {
	t.stats.add(StMsgsDropped)
	t.node.ReportUnreachable(m.GetTo())
	if m.GetType() == pb.MsgSnap {
		t.node.ReportSnapshot(m.GetTo(), raft.SnapshotFailure)
	}
}

// dial connects to p as a peer (helloPeer); nil if it cannot now.
func (t *Transport) dial(p *peer) net.Conn {
	t.stats.add(StDials)
	c, err := net.DialTimeout("tcp", p.addr, dialTimeout)
	if err != nil {
		t.stats.add(StConnErrors)
		return nil
	}
	disarm := closeAfter(c, writeTimeout)
	written := writeAll(c, []byte{helloPeer})
	if !disarm() || !written {
		t.stats.add(StConnErrors)
		c.Close()
		return nil
	}
	return c
}

// runPeer writes p's messages to a connection to p, in order, dialing one when it has none, until
// the transport stops (stop), and then closes its connection. A message whose connection cannot
// be made, or whose write fails, is dropped, and the connection closed (the next message
// redials). A snapshot is reported finished once its frame is written:
// the peer may still lose it (crash before it steps it), which raft then learns by the peer's
// answers, as with etcd's transport.
func (t *Transport) runPeer(p *peer) {
	var c net.Conn
	for {
		var m *pb.Message
		select {
		case m = <-p.queue:
		case <-t.stopc:
			if c != nil {
				c.Close()
			}
			return
		}
		if c == nil {
			c = t.dial(p)
		}
		if c == nil {
			t.dropped(m)
			continue
		}
		disarm := closeAfter(c, writeTimeout)
		written := writeFrame(c, putMsg(nil, m))
		if !disarm() || !written {
			t.stats.add(StConnErrors)
			c.Close()
			c = nil
			t.dropped(m)
			continue
		}
		t.stats.add(StMsgsSent)
		if m.GetType() == pb.MsgSnap {
			t.stats.add(StSnapshotsSent)
			t.node.ReportSnapshot(m.GetTo(), raft.SnapshotFinish)
		}
	}
}
