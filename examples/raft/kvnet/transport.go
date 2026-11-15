package kvnet

import (
	"context"
	"net"
	"time"

	"go.etcd.io/raft/v3"
	pb "go.etcd.io/raft/v3/raftpb"
)

// Faults are the faults the transport adds to the real network's (a connection refused while
// its target is down, reset when it crashes, a frame half written): each a probability 1/n, 0
// for none.
type Faults struct {
	Drop      uint64 // a message dropped before it is sent
	Delay     uint64 // a message sent later, after a random delay below 20ms (reordered)
	Duplicate uint64 // a message sent twice
	Cut       uint64 // the connection closed after a message is written (the next one redials)
}

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
// and hands the messages its listener receives to the node. A message is sent at most once
// (twice if Faults duplicates it), never retried: raft retransmits what matters. The node learns
// of a message dropped (ReportUnreachable) and of each snapshot's fate (ReportSnapshot, after its
// frame is written or dropped).
type Transport struct {
	id     uint64
	node   raft.Node
	faults Faults
	stats  *Stats
	peers  map[uint64]*peer // every other replica the program knows, read-only once started
}

// newTransport is the transport of node id, whose peers' addresses are addrs (by id; its own
// included, and left out: raft never sends to itself), with the faults f.
func newTransport(id uint64, addrs map[uint64]string, f Faults, stats *Stats) *Transport {
	t := &Transport{id: id, faults: f, stats: stats, peers: make(map[uint64]*peer)}
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

// chance is true with probability 1/n, never if n is 0.
func chance(n uint64) bool {
	return n != 0 && oneIn(n)
}

// Send hands each of ms to its peer's sender, without waiting; one to an unknown peer, or one
// whose peer's queue is full, is dropped.
func (t *Transport) Send(ms []*pb.Message) {
	for _, m := range ms {
		p, ok := t.peers[m.GetTo()]
		if !ok || chance(t.faults.Drop) {
			t.dropped(m)
			continue
		}
		if chance(t.faults.Delay) {
			t.stats.add(StMsgsDelayed)
			delay := time.Duration(below(20)) * time.Millisecond
			go func() {
				time.Sleep(delay)
				t.enqueue(p, m)
			}()
			continue
		}
		t.enqueue(p, m)
		if chance(t.faults.Duplicate) {
			t.stats.add(StMsgsDuplicated)
			t.enqueue(p, m)
		}
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
	c.SetWriteDeadline(time.Now().Add(writeTimeout))
	if !writeAll(c, []byte{helloPeer}) {
		t.stats.add(StConnErrors)
		c.Close()
		return nil
	}
	return c
}

// runPeer writes p's messages to a connection to p, in order, dialing one when it has none. A
// message whose connection cannot be made, or whose write fails, is dropped, and the connection
// closed (the next message redials). A snapshot is reported finished once its frame is written:
// the peer may still lose it (crash before it steps it), which raft then learns by the peer's
// answers, as with etcd's transport.
func (t *Transport) runPeer(p *peer) {
	var c net.Conn
	for m := range p.queue {
		if c == nil {
			c = t.dial(p)
		}
		if c == nil {
			t.dropped(m)
			continue
		}
		c.SetWriteDeadline(time.Now().Add(writeTimeout))
		if !writeFrame(c, putMsg(nil, m)) {
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
		if chance(t.faults.Cut) {
			c.Close()
			c = nil
		}
	}
}

// servePeer reads messages from a peer's connection and steps them on the node, until the
// connection fails or ends. A frame that does not decode, or a message not addressed to this
// node, ends the connection. A message the node does not take within stepTimeout is dropped.
func (t *Transport) servePeer(c net.Conn) {
	defer c.Close()
	for {
		b, ok := readFrame(c)
		if !ok {
			return
		}
		m, good := getMsg(b)
		if !good || m.GetTo() != t.id {
			t.stats.add(StBadFrames)
			return
		}
		t.stats.add(StMsgsReceived)
		ctx, cancel := context.WithTimeout(context.Background(), stepTimeout)
		t.node.Step(ctx, m)
		cancel()
	}
}
