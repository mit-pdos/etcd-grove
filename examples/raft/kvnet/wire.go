package kvnet

import (
	"encoding/binary"
	"net"

	pb "go.etcd.io/raft/v3/raftpb"
)

// maxFrame bounds a frame's length: a reader drops a connection that announces a longer one
// (a peer's garbage, not a message of this program's, whose snapshots are small).
const maxFrame = 1 << 26

// writeAll writes all of b to c; false on an error (the connection is then unusable).
func writeAll(c net.Conn, b []byte) bool {
	for len(b) != 0 {
		n, err := c.Write(b)
		if err != nil {
			return false
		}
		b = b[n:]
	}
	return true
}

// readFull reads exactly len(b) bytes from c into b; false on an error or the connection's end
// (a sender that crashed in the middle of a frame leaves it half written: it is dropped).
func readFull(c net.Conn, b []byte) bool {
	for len(b) != 0 {
		n, err := c.Read(b)
		if n == 0 && err != nil {
			return false
		}
		b = b[n:]
	}
	return true
}

// writeFrame writes body to c as one frame: its length (8 bytes, little-endian), then body. A body
// longer than maxFrame, which readFrame would refuse, is not written: false, nothing written.
func writeFrame(c net.Conn, body []byte) bool {
	if len(body) > maxFrame {
		return false
	}
	return writeAll(c, putBytes(make([]byte, 0, 8+len(body)), body))
}

// readFrame reads one frame from c and returns its body, a fresh slice; false on an error, the
// connection's end, or a length past maxFrame.
func readFrame(c net.Conn) ([]byte, bool) {
	var n [8]byte
	if !readFull(c, n[:]) {
		return nil, false
	}
	l := binary.LittleEndian.Uint64(n[:])
	if l > maxFrame {
		return nil, false
	}
	b := make([]byte, l)
	if !readFull(c, b) {
		return nil, false
	}
	return b, true
}

// The first byte a connection carries, which says what the dialer is.
const (
	helloPeer   = 'P' // a peer: raft messages follow, one per frame, never answered
	helloClient = 'C' // a client: one request frame, answered by one response frame
)

// putConfState appends cs to buf: the voters, learners, outgoing voters and next learners (each
// as putIDs writes them), then auto-leave (1 byte).
func putConfState(buf []byte, cs *pb.ConfState) []byte {
	buf = putIDs(buf, cs.GetVoters())
	buf = putIDs(buf, cs.GetLearners())
	buf = putIDs(buf, cs.GetVotersOutgoing())
	buf = putIDs(buf, cs.GetLearnersNext())
	if cs.GetAutoLeave() {
		return append(buf, 1)
	}
	return append(buf, 0)
}

// getConfState reads back what putConfState wrote at the start of b.
func getConfState(b []byte) (cs *pb.ConfState, rest []byte, ok bool) {
	voters, r1, ok1 := getIDs(b)
	learners, r2, ok2 := getIDs(r1)
	outgoing, r3, ok3 := getIDs(r2)
	next, r4, ok4 := getIDs(r3)
	if !ok1 || !ok2 || !ok3 || !ok4 || len(r4) < 1 {
		return nil, nil, false
	}
	return &pb.ConfState{Voters: voters, Learners: learners, VotersOutgoing: outgoing,
		LearnersNext: next, AutoLeave: new(r4[0] == 1)}, r4[1:], true
}

// putMsg appends m to buf: its type, to, from, term, log term, index, commit and vote (8 bytes
// each), reject (1 byte), reject hint (8 bytes), context (putBytes), entries (their number, then
// each as putEntry writes it), and its snapshot (1 byte, 0 if it has none, then putSnapshot). It
// leaves out m's Responses, which only a message a node sends itself has (never one in a Ready's
// Messages, with synchronous storage writes). The wire's copy, as kvdurable's copyMsg.
func putMsg(buf []byte, m *pb.Message) []byte {
	buf = putUint64(buf, uint64(m.GetType()))
	buf = putUint64(buf, m.GetTo())
	buf = putUint64(buf, m.GetFrom())
	buf = putUint64(buf, m.GetTerm())
	buf = putUint64(buf, m.GetLogTerm())
	buf = putUint64(buf, m.GetIndex())
	buf = putUint64(buf, m.GetCommit())
	buf = putUint64(buf, m.GetVote())
	if m.GetReject() {
		buf = append(buf, 1)
	} else {
		buf = append(buf, 0)
	}
	buf = putUint64(buf, m.GetRejectHint())
	buf = putBytes(buf, m.GetContext())
	buf = putUint64(buf, uint64(len(m.GetEntries())))
	for _, e := range m.GetEntries() {
		buf = putEntry(buf, e)
	}
	if m.Snapshot == nil {
		return append(buf, 0)
	}
	return putSnapshot(append(buf, 1), m.Snapshot)
}

// getMsg reads back what putMsg wrote, all of b; ok is false for bytes it did not write, or a
// message type raft does not have.
func getMsg(b []byte) (*pb.Message, bool) {
	var f [8]uint64
	rest := b
	for i := range f {
		x, r, ok := getUint64(rest)
		if !ok {
			return nil, false
		}
		f[i] = x
		rest = r
	}
	if _, known := pb.MessageType_name[int32(f[0])]; !known || f[0] > 1<<31 || len(rest) < 1 {
		return nil, false
	}
	reject := rest[0] == 1
	hint, r1, ok1 := getUint64(rest[1:])
	ctx, r2, ok2 := getBytes(r1)
	n, r3, ok3 := getUint64(r2)
	if !ok1 || !ok2 || !ok3 || n > uint64(len(r3)) {
		return nil, false
	}
	rest = r3
	ents := make([]*pb.Entry, 0, n)
	for i := uint64(0); i < n; i++ {
		e, r, ok := getMsgEntry(rest)
		if !ok {
			return nil, false
		}
		ents = append(ents, e)
		rest = r
	}
	if len(rest) < 1 {
		return nil, false
	}
	m := &pb.Message{Type: pb.MessageType(f[0]).Enum(), To: new(f[1]), From: new(f[2]), Term: new(f[3]),
		LogTerm: new(f[4]), Index: new(f[5]), Commit: new(f[6]), Vote: new(f[7]), Reject: new(reject),
		RejectHint: new(hint), Context: ctx, Entries: ents}
	if rest[0] == 1 {
		snap, r, ok := getSnapshot(rest[1:])
		if !ok {
			return nil, false
		}
		m.Snapshot = snap
		rest = r
	} else {
		rest = rest[1:]
	}
	return m, len(rest) == 0
}

// getMsgEntry reads back what putEntry wrote at the start of b, an entry of a message, of any type
// (an EntryType is an int32, which putEntry wrote sign-extended and the conversion truncates back):
// getEntry, which reads a file, refuses a type raft does not have; a message's entries are whatever
// raft sent.
func getMsgEntry(b []byte) (e *pb.Entry, rest []byte, ok bool) {
	term, r1, ok1 := getUint64(b)
	index, r2, ok2 := getUint64(r1)
	typ, r3, ok3 := getUint64(r2)
	if !ok1 || !ok2 || !ok3 {
		return nil, nil, false
	}
	data, r4, ok4 := getBytes(r3)
	if !ok4 {
		return nil, nil, false
	}
	return &pb.Entry{Term: new(term), Index: new(index), Type: pb.EntryType(typ).Enum(), Data: data}, r4, true
}
