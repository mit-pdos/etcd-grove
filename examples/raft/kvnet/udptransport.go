package kvnet

import (
	"encoding/binary"
	"net"
	"sync"
	"time"

	"go.etcd.io/raft/v3"
	pb "go.etcd.io/raft/v3/raftpb"
)

// The UDP transport (kvudp): the raft messages between replicas go as UDP datagrams instead of
// over TCP connections (Transport), the clients' requests still over TCP. The network may lose,
// duplicate, reorder and delay any datagram; one of at most maxDatagram bytes that arrives arrives
// intact (a longer one may arrive as garbage: none is ever sent). So a message is encoded (putMsg),
// cut into chunks, and each chunk sent as a fragment datagram, which names the message by its
// sender's id, the sender's process's boot number and the message's sequence number in that
// process; the receiver reassembles the message from the fragments of that name. The name is
// never reused across the cluster's life (the boot number is durable: nextBoot), so the receiver
// never mixes the fragments of two messages into one nobody sent. A snapshot (MsgSnap) is
// reported finished only once its receiver acknowledges it (an ack datagram); unacknowledged, it
// is sent again a few times, then reported failed (even if it was delivered and only its
// acknowledgments were lost).
//
// The network is used only through net.ListenUDP (once per process, never closed),
// (*net.UDPConn).WriteToUDP and (*net.UDPConn).ReadFromUDP, every address built here from the
// replicas' address strings (udpAddr), never from what ReadFromUDP returns.

// The datagram format. Every datagram starts with the header: udpMagic (4 bytes), its kind (1
// byte), from, to, boot and seq (8 bytes each); every integer little-endian.
//
//   - A fragment (kindFragment): the header, then index and total (4 bytes each), then the chunk
//     (1 to chunkSize bytes, the rest of the datagram): the index-th of the total chunks of the
//     message (boot, seq) of replica from, to replica to.
//   - An ack (kindAck): the header alone, from replica from (the message's receiver) to replica to
//     (its sender): replica to's message (boot, seq) was received.
//
// maxDatagram is the largest datagram that arrives intact: 552, Linux's floor of the path MTU (a
// forged ICMP message can bring it down there), less the IPv4 and UDP headers (28). chunkSize is
// maxDatagram less the fragment's header (fragHeaderLen, 45).
const (
	maxDatagram   = 524
	chunkSize     = 479
	udpMagic      = 0x4455564b
	kindFragment  = 1
	kindAck       = 2
	ackLen        = 4 + 1 + 4*8            // an ack's length, the header's
	fragHeaderLen = ackLen + 4 + 4         // a fragment's length before its chunk
	maxFragments  = 1 << 14                // the most fragments of a message (a longer message is dropped)
	maxUint64     = 1<<64 - 1              // the largest boot and sequence numbers (never used)
	maxPending    = 8                      // the most messages being reassembled per sender
	maxDone       = 64                     // the most completed messages remembered per sender
	staleLag      = 1 << 16                // a message in progress this far behind one completed is stale
	snapAckWait   = 300 * time.Millisecond // how long a snapshot waits for its ack, per send
	snapResends   = 3                      // how many times an unacknowledged snapshot is sent again
)

// datagram is a datagram read back (getDatagram): an ack's fields, and a fragment's.
type datagram struct {
	kind  byte
	from  uint64
	to    uint64
	boot  uint64
	seq   uint64
	index uint32
	total uint32
	chunk []byte
}

// putUint32 appends x to buf in little-endian order, as putUint64 does for 64 bits (PutUint32 into
// a local array, then append: binary.LittleEndian.AppendUint32 has no spec in Perennial).
func putUint32(buf []byte, x uint32) []byte {
	var n [4]byte
	binary.LittleEndian.PutUint32(n[:], x)
	return append(buf, n[:]...)
}

// putHeader appends the header of a datagram of the given kind to buf.
func putHeader(buf []byte, kind byte, from, to, boot, seq uint64) []byte {
	buf = putUint32(buf, udpMagic)
	buf = append(buf, kind)
	buf = putUint64(buf, from)
	buf = putUint64(buf, to)
	buf = putUint64(buf, boot)
	return putUint64(buf, seq)
}

// putFragment is a fragment: chunk, the index-th of total, of message (boot, seq) from from to to.
func putFragment(from, to, boot, seq uint64, index, total uint32, chunk []byte) []byte {
	buf := putHeader(make([]byte, 0, fragHeaderLen+len(chunk)), kindFragment, from, to, boot, seq)
	buf = putUint32(buf, index)
	buf = putUint32(buf, total)
	return append(buf, chunk...)
}

// putAck is the ack of message (boot, seq) of replica to, which replica from received.
func putAck(from, to, boot, seq uint64) []byte {
	return putHeader(make([]byte, 0, ackLen), kindAck, from, to, boot, seq)
}

// getDatagram reads back what putFragment or putAck wrote, all of b; ok is false for anything
// else (a fragment whose chunk is empty or longer than chunkSize, or whose index is not below its
// total, or whose total is 0 or above maxFragments, included). The chunk is a copy.
func getDatagram(b []byte) (datagram, bool) {
	var d datagram
	if len(b) < ackLen || binary.LittleEndian.Uint32(b) != udpMagic {
		return d, false
	}
	d.kind = b[4]
	d.from = binary.LittleEndian.Uint64(b[5:])
	d.to = binary.LittleEndian.Uint64(b[13:])
	d.boot = binary.LittleEndian.Uint64(b[21:])
	d.seq = binary.LittleEndian.Uint64(b[29:])
	if d.kind == kindAck {
		return d, len(b) == ackLen
	}
	if d.kind != kindFragment || len(b) <= fragHeaderLen || len(b) > fragHeaderLen+chunkSize {
		return d, false
	}
	d.index = binary.LittleEndian.Uint32(b[ackLen:])
	d.total = binary.LittleEndian.Uint32(b[ackLen+4:])
	if d.total == 0 || d.total > maxFragments || d.index >= d.total {
		return d, false
	}
	d.chunk = append([]byte(nil), b[fragHeaderLen:]...)
	return d, true
}

// fragments are the fragments of message (boot, seq), body, from from to to: body cut into chunks
// of chunkSize bytes (the last one shorter), each at most maxDatagram bytes; nil if body is empty
// or needs more than maxFragments of them.
func fragments(from, to, boot, seq uint64, body []byte) [][]byte {
	n := (uint64(len(body)) + chunkSize - 1) / chunkSize
	if n == 0 || n > maxFragments {
		return nil
	}
	var ds [][]byte
	for i := uint64(0); i < n; i++ {
		end := (i + 1) * chunkSize
		if end > uint64(len(body)) {
			end = uint64(len(body))
		}
		ds = append(ds, putFragment(from, to, boot, seq, uint32(i), uint32(n), body[i*chunkSize:end]))
	}
	return ds
}

// parseAddr is the IPv4 address (4 bytes) and the port of a, an address AddrOk accepts
// (a.b.c.d:p); ok is false for any other string.
func parseAddr(a string) (ip [4]byte, port uint64, ok bool) {
	if !AddrOk(a) {
		return ip, 0, false
	}
	var v [5]uint64
	n := 0
	start := 0
	for i := 0; i <= len(a); i++ {
		if i == len(a) || a[i] == '.' || a[i] == ':' {
			x, good := decimal(a[start:i], 65535)
			if !good || n >= 5 {
				return ip, 0, false
			}
			v[n] = x
			n++
			start = i + 1
		}
	}
	if n != 5 || v[0] > 255 || v[1] > 255 || v[2] > 255 || v[3] > 255 {
		return ip, 0, false
	}
	return [4]byte{byte(v[0]), byte(v[1]), byte(v[2]), byte(v[3])}, v[4], true
}

// udpAddr is a as a UDP address (parseAddr); false if AddrOk refuses a.
func udpAddr(a string) (*net.UDPAddr, bool) {
	ip, port, ok := parseAddr(a)
	if !ok {
		return nil, false
	}
	return &net.UDPAddr{IP: []byte{ip[0], ip[1], ip[2], ip[3]}, Port: int(port)}, true
}

// msgID names a message of a given sender: its process's boot number and its sequence number there.
type msgID struct {
	boot uint64
	seq  uint64
}

// partial is a message being reassembled: its chunks (nil where none has arrived yet), how many
// have arrived, and the highest index arrived.
type partial struct {
	id     msgID
	chunks [][]byte
	have   uint32
	top    uint32
}

// doneMsg is a message completed: its name, and whether it was a snapshot (whose duplicates are
// acknowledged again).
type doneMsg struct {
	id   msgID
	snap bool
}

// reassembler reassembles the messages from their fragments, per sender, in bounded memory: at
// most maxPending messages in progress per sender (a new one evicts the oldest, incomplete for
// good: a fragment was lost, or is late; and a message completed evicts those in progress that are
// stale, of an earlier process of its sender or more than staleLag sequence numbers behind it), and
// the names of the last maxDone completed (a fragment
// of one of them is a duplicate, dropped). It counts in stats.
type reassembler struct {
	pending map[uint64][]*partial
	done    map[uint64][]doneMsg
	last    map[uint64]msgID // per sender, the latest message completed
	stats   *Stats
}

func newReassembler(stats *Stats) *reassembler {
	return &reassembler{pending: make(map[uint64][]*partial), done: make(map[uint64][]doneMsg),
		last: make(map[uint64]msgID), stats: stats}
}

// add adds fragment d (getDatagram's, of kind kindFragment). If it completes its message, add
// returns the message's body and complete true; the caller then remembers it (remember). reack is
// true if d is the first fragment of a snapshot already completed (its ack is to be sent again).
func (r *reassembler) add(d datagram) (body []byte, complete bool, reack bool) {
	id := msgID{boot: d.boot, seq: d.seq}
	for _, x := range r.done[d.from] {
		if x.id == id {
			r.stats.add(StUDPFragmentsDuplicate)
			return nil, false, x.snap && d.index == 0
		}
	}
	ps := r.pending[d.from]
	var p *partial
	for _, x := range ps {
		if x.id == id {
			p = x
		}
	}
	if p == nil {
		if len(ps) >= maxPending {
			r.stats.add(StUDPReassembliesEvicted)
			ps = append([]*partial(nil), ps[1:]...)
		}
		p = &partial{id: id, chunks: make([][]byte, d.total), top: d.index}
		ps = append(ps, p)
		r.pending[d.from] = ps
	}
	if uint64(len(p.chunks)) != uint64(d.total) || d.index >= d.total {
		r.stats.add(StUDPBadDatagrams)
		return nil, false, false
	}
	if p.chunks[d.index] != nil {
		r.stats.add(StUDPFragmentsDuplicate)
		return nil, false, false
	}
	if d.index < p.top {
		r.stats.add(StUDPFragmentsReordered)
	} else {
		p.top = d.index
	}
	p.chunks[d.index] = d.chunk
	p.have++
	if p.have < d.total {
		return nil, false, false
	}
	var rest []*partial
	for _, x := range ps {
		if x != p {
			rest = append(rest, x)
		}
	}
	r.pending[d.from] = rest
	for _, c := range p.chunks {
		body = append(body, c...)
	}
	if d.total > 1 {
		r.stats.add(StUDPMultiFragment)
	}
	return body, true, false
}

// remember records that message id of sender from was completed, and whether it is a snapshot,
// and evicts from's stale messages in progress: of an earlier boot (that process is gone: its
// fragments still to come can only be late copies), or more than staleLag messages older (a
// snapshot is sent again for snapAckWait*(snapResends+1) at most, which takes fewer).
func (r *reassembler) remember(from uint64, id msgID, snap bool) {
	ds := r.done[from]
	if len(ds) >= maxDone {
		ds = append([]doneMsg(nil), ds[1:]...)
	}
	r.done[from] = append(ds, doneMsg{id: id, snap: snap})
	var keep []*partial
	for _, p := range r.pending[from] {
		if p.id.boot < id.boot || (p.id.boot == id.boot && p.id.seq < id.seq && id.seq-p.id.seq > staleLag) {
			r.stats.add(StUDPReassembliesEvicted)
		} else {
			keep = append(keep, p)
		}
	}
	r.pending[from] = keep
	l, ok := r.last[from]
	if ok && l.boot == id.boot && id.seq < l.seq {
		r.stats.add(StUDPMsgsReordered)
		return
	}
	r.last[from] = id
}

// ackWait is a snapshot waiting for its ack: its receiver, and the channel closed when the ack
// arrives.
type ackWait struct {
	to   uint64
	done chan struct{}
}

// udpNet is a replica's process's UDP endpoint, shared by its incarnations: its socket, every
// replica's address, the process's boot number, the last sequence number used, and the snapshots
// waiting for their acks (by sequence number). Its receiver (udpNet.receive) is one goroutine per
// process.
type udpNet struct {
	id    uint64
	conn  *net.UDPConn
	addrs map[uint64]*net.UDPAddr // every replica's whose address is well formed, its own included
	boot  uint64
	mu    sync.Mutex
	seq   uint64
	acks  map[uint64]*ackWait
}

// nextSeq is a sequence number never used before in this process; false once they are used up.
func (u *udpNet) nextSeq() (uint64, bool) {
	u.mu.Lock()
	defer u.mu.Unlock()
	if u.seq == maxUint64 {
		return 0, false
	}
	u.seq++
	return u.seq, true
}

// expectAck registers snapshot seq, sent to replica to, as waiting for its ack: the channel
// returned is closed when it arrives (acked).
func (u *udpNet) expectAck(to, seq uint64) chan struct{} {
	w := &ackWait{to: to, done: make(chan struct{})}
	u.mu.Lock()
	u.acks[seq] = w
	u.mu.Unlock()
	return w.done
}

// forgetAck stops waiting for snapshot seq's ack.
func (u *udpNet) forgetAck(seq uint64) {
	u.mu.Lock()
	delete(u.acks, seq)
	u.mu.Unlock()
}

// acked takes the ack of this process's message seq from replica from: if a snapshot sent to from
// waits for it, it wakes it (once) and says true.
func (u *udpNet) acked(from, seq uint64) bool {
	u.mu.Lock()
	defer u.mu.Unlock()
	w, ok := u.acks[seq]
	if !ok || w.to != from {
		return false
	}
	delete(u.acks, seq)
	close(w.done)
	return true
}

// write sends datagram b to replica to; false if it has no address or the write fails.
func (u *udpNet) write(to uint64, b []byte) bool {
	a, ok := u.addrs[to]
	if !ok {
		return false
	}
	_, err := u.conn.WriteToUDP(b, a)
	return err == nil
}

// udpPeer is the sending side towards one peer: the messages waiting, which its goroutine
// (udpTransport.runPeer) sends in order.
type udpPeer struct {
	id    uint64
	queue chan *pb.Message
}

// udpTransport is an incarnation's sending side over the process's UDP endpoint (a
// peerTransport): a queue and a goroutine per peer, as Transport's, and a goroutine per snapshot,
// which waits for its ack. A message is sent once (a snapshot a few times, until acknowledged),
// never otherwise retried: raft retransmits what matters. The node learns of a message dropped
// (ReportUnreachable) and of each snapshot's fate (ReportSnapshot: finished once acknowledged,
// failed if not after every resend, or dropped).
type udpTransport struct {
	u     *udpNet
	node  raft.Node
	stats *Stats
	peers map[uint64]*udpPeer // every other replica with an address, read-only once started
	stopc chan struct{}       // closed by stop: the senders and snapshot waiters return
}

// newTransport is the incarnation's transport over u, as a newPeerTransport (u's replica's: id
// and addrs are u's).
func (u *udpNet) newTransport(id uint64, addrs map[uint64]string, stats *Stats) peerTransport {
	t := &udpTransport{u: u, stats: stats, peers: make(map[uint64]*udpPeer), stopc: make(chan struct{})}
	for pid := range u.addrs {
		if pid != u.id {
			t.peers[pid] = &udpPeer{id: pid, queue: make(chan *pb.Message, queueLen)}
		}
	}
	return t
}

// start starts the senders, a goroutine per peer, once the node exists.
func (t *udpTransport) start(node raft.Node) {
	t.node = node
	for _, p := range t.peers {
		go t.runPeer(p)
	}
}

// stop ends the senders and the snapshot waiters (the incarnation's node is stopped), leaving what
// the queues hold unsent.
func (t *udpTransport) stop() {
	close(t.stopc)
}

// Send hands each of ms to its peer's sender, without waiting; one to an unknown peer, or one
// whose peer's queue is full, is dropped.
func (t *udpTransport) Send(ms []*pb.Message) {
	for _, m := range ms {
		p, ok := t.peers[m.GetTo()]
		if !ok {
			t.dropped(m)
			continue
		}
		select {
		case p.queue <- m:
		default:
			t.dropped(m)
		}
	}
}

// dropped tells the node that m was not sent.
func (t *udpTransport) dropped(m *pb.Message) {
	t.stats.add(StMsgsDropped)
	t.node.ReportUnreachable(m.GetTo())
	if m.GetType() == pb.MsgSnap {
		t.node.ReportSnapshot(m.GetTo(), raft.SnapshotFailure)
	}
}

// writeAll sends the datagrams ds to replica to; false at the first that fails.
func (t *udpTransport) writeAll(to uint64, ds [][]byte) bool {
	for _, d := range ds {
		if !t.u.write(to, d) {
			t.stats.add(StUDPWriteErrors)
			return false
		}
		t.stats.add(StUDPFragmentsSent)
	}
	return true
}

// runPeer sends p's messages, in order, each under a new sequence number, until the transport
// stops. A message that cannot be cut into fragments (too long), or whose fragment cannot be
// written, is dropped. A snapshot is handed to a goroutine of its own (sendSnapshot), which waits
// for its ack.
func (t *udpTransport) runPeer(p *udpPeer) {
	for {
		var m *pb.Message
		select {
		case m = <-p.queue:
		case <-t.stopc:
			return
		}
		seq, ok := t.u.nextSeq()
		var ds [][]byte
		if ok {
			ds = fragments(t.u.id, p.id, t.u.boot, seq, putMsg(nil, m))
		}
		if ds == nil {
			t.dropped(m)
			continue
		}
		if m.GetType() == pb.MsgSnap {
			t.stats.add(StSnapshotsSent)
			go t.sendSnapshot(p.id, seq, ds)
			continue
		}
		if !t.writeAll(p.id, ds) {
			t.dropped(m)
			continue
		}
		t.stats.add(StMsgsSent)
	}
}

// timer is a channel that receives once, d from now (a timer: nothing reads the clock).
func timer(d time.Duration) chan struct{} {
	c := make(chan struct{}, 1)
	time.AfterFunc(d, func() { c <- struct{}{} })
	return c
}

// sendSnapshot sends the snapshot whose fragments are ds, message seq, to replica to, and waits for
// its ack: it reports the snapshot finished when the ack comes, and sends it again after
// snapAckWait without one, up to snapResends times, then reports it failed. It returns without a
// report if the transport stops meanwhile.
func (t *udpTransport) sendSnapshot(to, seq uint64, ds [][]byte) {
	done := t.u.expectAck(to, seq)
	defer t.u.forgetAck(seq)
	for try := uint64(0); try <= snapResends; try++ {
		if try != 0 {
			t.stats.add(StUDPSnapshotResends)
		}
		// a failed write is a lost datagram: it waits for the ack all the same
		t.writeAll(to, ds)
		select {
		case <-done:
			t.stats.add(StMsgsSent)
			t.stats.add(StUDPSnapshotsAcked)
			t.node.ReportSnapshot(to, raft.SnapshotFinish)
			return
		case <-timer(snapAckWait):
		case <-t.stopc:
			return
		}
	}
	t.stats.add(StUDPSnapshotsFailed)
	t.node.ReportSnapshot(to, raft.SnapshotFailure)
}
