package kvnet

import (
	"net"
	"time"

	"github.com/mit-pdos/etcd-grove/examples/lib/durable"
	pb "go.etcd.io/raft/v3/raftpb"
)

// BootFileOf is the durable file of replica id's boot counter (nextBoot) in the directory dir.
func BootFileOf(dir string, id uint64) string {
	return dir + "/udp-boot-" + itoa(id)
}

// nextBoot is the boot number of this process of replica id, whose directory is dir: one more
// than the last process's (the counter's file holds it, 8 bytes; 0 if there is no file), written
// durably before it is returned, so that no two processes of the replica ever have the same. It
// panics on a file this package did not write. (It never returns once the counter is at its
// largest value, which 2^64 - 1 processes would take.)
func nextBoot(dir string, id uint64) uint64 {
	file := BootFileOf(dir, id)
	boot := uint64(0)
	if data, ok := durable.Read(file); ok {
		b, _, good := getUint64([]byte(data))
		if !good || len(data) != 8 {
			panic("kvnet: a boot file this package did not write")
		}
		boot = b
	}
	for boot == maxUint64 {
		time.Sleep(time.Second)
	}
	durable.Write(file, string(putUint64(nil, boot+1)))
	return boot + 1
}

// listenUDP opens the process's UDP socket at a, retrying until it can (the previous process's
// socket may not be gone yet): a failed ListenUDP is never a panic.
func listenUDP(a *net.UDPAddr) *net.UDPConn {
	for {
		c, err := net.ListenUDP("udp4", a)
		if err == nil {
			return c
		}
		time.Sleep(10 * time.Millisecond)
	}
}

// openUDP is replica cfg.ID's process's UDP endpoint: its socket at its own address (the same
// string as its TCP listener's), opened once and never closed, and the process's boot number
// (nextBoot). A replica whose address is not well formed is left out of the endpoint's addresses
// (never sent to); it panics if the replica's own is not (RunNodeUDP checks it is).
func openUDP(cfg NodeConfig) *udpNet {
	addrs := make(map[uint64]*net.UDPAddr)
	for id, a := range cfg.Addrs {
		if ua, ok := udpAddr(a); ok {
			addrs[id] = ua
		}
	}
	self, ok := addrs[cfg.ID]
	if !ok {
		panic("kvnet: not a valid address of its own")
	}
	conn := listenUDP(self)
	boot := nextBoot(cfg.Dir, cfg.ID)
	return &udpNet{id: cfg.ID, conn: conn, addrs: addrs, boot: boot, acks: make(map[uint64]*ackWait)}
}

// RunNodeUDP is RunNode with the raft messages between replicas over UDP (RunUDP).
func RunNodeUDP(id uint64, addrs string, dir string, voters uint64, preVote, checkQuorum, stepDownOnRemoval bool,
	maxSizePerMsg, maxCommittedSizePerReady, maxInflightMsgs uint64) {
	as := SplitAddrs(addrs)
	if !ValidCluster(as, voters, maxSizePerMsg, maxCommittedSizePerReady, maxInflightMsgs) ||
		id < 1 || id > uint64(len(as)) {
		panic("kvnet: not a valid cluster")
	}
	m := make(map[uint64]string)
	for i, a := range as {
		m[uint64(i)+1] = a
	}
	RunUDP(NodeConfig{ID: id, Dir: dir, Addrs: m, Opts: Options{
		Voters: voters, PreVote: preVote, CheckQuorum: checkQuorum, StepDownOnRemoval: stepDownOnRemoval,
		MaxSizePerMsg: maxSizePerMsg, MaxCommittedSizePerReady: maxCommittedSizePerReady,
		MaxInflightMsgs: int(maxInflightMsgs)}})
}

// RunUDP is Run with the raft messages between replicas over UDP: it listens for its clients on
// its address (TCP), opens its UDP endpoint at the same address (openUDP), starts the replica
// with the UDP transport (whose endpoint, receiver, boot number and sequence numbers every
// incarnation of the process shares), receives its peers' datagrams (udpNet.receive) and serves
// its clients. It never returns.
func RunUDP(cfg NodeConfig) {
	l := listen(cfg.Addrs[cfg.ID])
	n, u := startNodeUDP(cfg)
	go u.receive(n)
	n.accept(l)
}

// startNodeUDP is StartNode with the UDP transport, over the endpoint it opens (openUDP), which it
// returns: its receiver is not started (udpNet.receive).
func startNodeUDP(cfg NodeConfig) (*Node, *udpNet) {
	u := openUDP(cfg)
	return startNode(cfg, u.newTransport), u
}

// received is a message received from a peer, to step: the message, and its name (the fragments'
// sender, boot and sequence numbers), with whether it is a snapshot (acknowledged once stepped).
type received struct {
	m    *pb.Message
	from uint64
	boot uint64
	seq  uint64
	snap bool
}

// receive reads the process's datagrams and handles each (handle), forever: one goroutine per
// process, across its incarnations. A failed read is retried. The messages it completes are
// stepped by a goroutine per peer (stepper), from a queue of queueLen messages: so that the reading
// never waits on the node, as the TCP transport's connections each have a goroutine of their own.
func (u *udpNet) receive(n *Node) {
	r := newReassembler(n.stats)
	steps := make(map[uint64]chan received)
	for id := range u.addrs {
		if id != u.id {
			q := make(chan received, queueLen)
			steps[id] = q
			go u.stepper(n, q)
		}
	}
	buf := make([]byte, maxDatagram)
	for {
		k, _, err := u.conn.ReadFromUDP(buf)
		if err != nil {
			time.Sleep(time.Millisecond)
			continue
		}
		u.handle(n, r, steps, buf[:k])
	}
}

// stepper steps the messages of q, in order, on the current incarnation (Node.stepPeer), and
// acknowledges each snapshot once stepped, forever.
func (u *udpNet) stepper(n *Node, q chan received) {
	for {
		x := <-q
		n.stepPeer(x.m)
		if x.snap {
			u.ack(n, x.from, x.boot, x.seq)
		}
	}
}

// ack sends the ack of message (boot, seq) of replica to.
func (u *udpNet) ack(n *Node, to, boot, seq uint64) {
	if u.write(to, putAck(u.id, to, boot, seq)) {
		n.stats.add(StUDPAcksSent)
	} else {
		n.stats.add(StUDPWriteErrors)
	}
}

// handle handles datagram b. A datagram that is malformed, not addressed to this replica, or
// from an unknown replica or itself is dropped. An ack wakes the snapshot waiting for it, if any.
// A fragment goes to the reassembler; a message it completes is decoded (getMsg) and, if it is
// addressed to this replica, queued to its sender's stepper (steps), or
// dropped if that queue is full (the stepper acknowledges a snapshot to its sender, at the
// sender's address by id, once stepped). The first fragment of a snapshot completed before is
// acknowledged again.
func (u *udpNet) handle(n *Node, r *reassembler, steps map[uint64]chan received, b []byte) {
	d, ok := getDatagram(b)
	_, known := u.addrs[d.from]
	if !ok || d.to != u.id || !known || d.from == u.id {
		n.stats.add(StUDPBadDatagrams)
		return
	}
	if d.kind == kindAck {
		if d.boot == u.boot && u.acked(d.from, d.seq) {
			n.stats.add(StUDPAcksReceived)
		}
		return
	}
	n.stats.add(StUDPFragmentsReceived)
	body, complete, reack := r.add(d)
	if reack {
		u.ack(n, d.from, d.boot, d.seq)
	}
	if !complete {
		return
	}
	m, good := getMsg(body)
	// Only m.To is checked, as Transport.servePeer does: not m.From, which is not always the
	// sender's (a follower forwards a MsgTransferLeader to its leader with From the transferee's),
	// and which the message's validity does not rest on (the fragments' header names the message,
	// and the reassembly is by that name).
	good = good && m.GetTo() == u.id
	snap := good && m.GetType() == pb.MsgSnap
	r.remember(d.from, msgID{boot: d.boot, seq: d.seq}, snap)
	if !good {
		n.stats.add(StUDPBadDatagrams)
		return
	}
	q, ok := steps[d.from]
	if !ok {
		n.stats.add(StUDPBadDatagrams)
		return
	}
	select {
	case q <- received{m: m, from: d.from, boot: d.boot, seq: d.seq, snap: snap}:
	default:
		n.stats.add(StUDPReceivedDropped)
	}
}
