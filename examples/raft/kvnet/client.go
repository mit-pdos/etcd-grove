package kvnet

import (
	"net"
	"time"

	pb "go.etcd.io/raft/v3/raftpb"
)

// The operations' kinds, for the clients.
const (
	OpPut  = opPut
	OpGet  = opGet
	OpRead = opRead
)

// EncodeOp is the operation of id id (the client's: never reused), kind OpPut or OpGet, key and
// value, as ReqPropose's payload (and the log entry it becomes).
func EncodeOp(id uint64, kind byte, key, val string) []byte {
	return encode(id, kind, key, val)
}

// EncodeRead is ReqRead's payload: the read's sequence number (the client's: never reused) and
// key.
func EncodeRead(seq uint64, key string) []byte {
	return putBytes(putUint64(nil, seq), []byte(key))
}

// EncodeDisrupt is ReqDisrupt's payload.
func EncodeDisrupt(what, to uint64) []byte {
	return putUint64(putUint64(nil, what), to)
}

// Request sends one request of kind to the replica at addr, with the given timeout (the
// replica's, for its answer), and returns its answer; false if it has none, or the replica cannot
// be reached, or does not answer within the timeout and a margin.
func Request(addr string, kind byte, timeout time.Duration, payload []byte) ([]byte, bool) {
	c, err := net.DialTimeout("tcp", addr, dialTimeout)
	if err != nil {
		return nil, false
	}
	defer c.Close()
	c.SetDeadline(time.Now().Add(timeout + 500*time.Millisecond))
	req := putUint64([]byte{kind}, uint64(timeout/time.Millisecond))
	req = append(req, payload...)
	if !writeAll(c, []byte{helloClient}) || !writeFrame(c, req) {
		return nil, false
	}
	b, ok := readFrame(c)
	if !ok || len(b) < 1 || b[0] != 1 {
		return nil, false
	}
	return b[1:], true
}

// PutConfChange appends cc to buf: 1 byte (1 for a ConfChange, 2 for a ConfChangeV2), then, for
// a ConfChange, its type and node id (8 bytes each); for a ConfChangeV2, its transition, the
// number of its changes, and each change's type and node id (8 bytes each).
func PutConfChange(buf []byte, cc pb.ConfChangeI) []byte {
	if v1, ok := cc.(*pb.ConfChange); ok {
		buf = append(buf, 1)
		buf = putUint64(buf, uint64(v1.GetType()))
		return putUint64(buf, v1.GetNodeId())
	}
	v2 := cc.AsV2()
	buf = append(buf, 2)
	buf = putUint64(buf, uint64(v2.GetTransition()))
	buf = putUint64(buf, uint64(len(v2.GetChanges())))
	for _, c := range v2.GetChanges() {
		buf = putUint64(buf, uint64(c.GetType()))
		buf = putUint64(buf, c.GetNodeId())
	}
	return buf
}

// GetConfChange reads back what PutConfChange wrote, all of b.
func GetConfChange(b []byte) (pb.ConfChangeI, bool) {
	if len(b) < 1 {
		return nil, false
	}
	if b[0] == 1 {
		t, r1, ok1 := getUint64(b[1:])
		id, r2, ok2 := getUint64(r1)
		if !ok1 || !ok2 || t > 3 || len(r2) != 0 {
			return nil, false
		}
		return &pb.ConfChange{Type: pb.ConfChangeType(t).Enum(), NodeId: new(id)}, true
	}
	tr, r1, ok1 := getUint64(b[1:])
	n, rest, ok2 := getUint64(r1)
	if b[0] != 2 || !ok1 || !ok2 || tr > 2 || n > uint64(len(rest))/16 {
		return nil, false
	}
	cc := &pb.ConfChangeV2{Transition: pb.ConfChangeTransition(tr).Enum()}
	for i := uint64(0); i < n; i++ {
		t, r2, _ := getUint64(rest)
		id, r3, _ := getUint64(r2)
		if t > 3 {
			return nil, false
		}
		cc.Changes = append(cc.Changes, &pb.ConfChangeSingle{Type: pb.ConfChangeType(t).Enum(), NodeId: new(id)})
		rest = r3
	}
	return cc, len(rest) == 0
}

// PutStatus appends s to buf.
func PutStatus(buf []byte, s Status) []byte {
	buf = putUint64(buf, s.Index)
	buf = putConfState(buf, s.Conf)
	buf = putMap(buf, s.Contents)
	for _, x := range []uint64{s.Lead, s.Term, s.Role, s.Commit} {
		buf = putUint64(buf, x)
	}
	buf = putUint64(buf, NumStats)
	for _, x := range s.Stats {
		buf = putUint64(buf, x)
	}
	return buf
}

// GetStatus reads back what PutStatus wrote.
func GetStatus(b []byte) (Status, bool) {
	var s Status
	index, r1, ok1 := getUint64(b)
	cs, r2, ok2 := getConfState(r1)
	kv, r3, ok3 := getMap(r2)
	if !ok1 || !ok2 || !ok3 {
		return s, false
	}
	s.Index, s.Conf, s.Contents = index, cs, kv
	var f [5]uint64
	rest := r3
	for i := range f {
		x, r, ok := getUint64(rest)
		if !ok {
			return s, false
		}
		f[i] = x
		rest = r
	}
	s.Lead, s.Term, s.Role, s.Commit = f[0], f[1], f[2], f[3]
	if f[4] != NumStats {
		return s, false
	}
	for i := range s.Stats {
		x, r, ok := getUint64(rest)
		if !ok {
			return s, false
		}
		s.Stats[i] = x
		rest = r
	}
	return s, len(rest) == 0
}
