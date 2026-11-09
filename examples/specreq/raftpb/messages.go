// Package raftpb holds the requirement snippets of raft's protobuf messages (batch 3h):
// Spec/go_etcd_io/raft/v3/raftpb/.
package raftpb

import (
	pb "go.etcd.io/raft/v3/raftpb"
	"google.golang.org/protobuf/proto"
)

// REQ raftpb/getters-nil: every getter reads through a nil message (raft's `snap.GetMetadata().
// GetIndex()` on a message without a snapshot; `IsEmptySnap` of a nil snapshot).
// Users: raft.go:1859 (handleSnapshot), node.go (IsEmptySnap), rafthttp's snapshot sender.
// Assumes: m is nil or a message held by msgPts (any fraction).
// Specs: Message.GetSnapshot.spec, Snapshot.GetMetadata.spec, SnapshotMetadata.GetIndex.spec (their
// nil conjuncts).
func ReqGettersNil(m *pb.Message) uint64 {
	if m.GetSnapshot().GetMetadata().GetIndex() != 0 && m.GetSnapshot() == nil {
		panic("getter through nil")
	}
	var e *pb.Entry
	if e.GetIndex() != 0 || e.GetData() != nil {
		panic("nil entry getter")
	}
	return m.GetSnapshot().GetMetadata().GetIndex()
}

// REQ raftpb/reply-shares-cell: a reply built from a request shares its `From` cell as its `To`;
// both messages stay readable and the request's reads do not change (raft.go:1841,
// `&pb.Message{To: m.From, ...}`).
// Users: raft.go:1841 (handleHeartbeat), raft.go:1874 (handleSnapshot), every handle* reply.
// Specs: msgPts_unfold.spec (cells read-only for good), pbRest_zero.spec, MessageType.Enum.spec,
// Message.GetTo.spec, Message.GetFrom.spec.
func ReqReplySharesCell(m *pb.Message) *pb.Message {
	from := m.GetFrom()
	r := &pb.Message{To: m.From, Type: pb.MsgHeartbeatResp.Enum(), Context: m.GetContext()}
	if r.GetTo() != from || m.GetFrom() != from {
		panic("shared cell changed")
	}
	return r
}

// REQ raftpb/field-write: an owned message's field is replaced by a fresh cell (node.go:388,
// raft.go:1743): the getter reads the new value, nothing else changes.
// Users: node.go:388 (m.From = new(r.id)), raft.go:1743/1762/1784 (m.To = new(r.lead)),
// rawnode.go:238 (m.Term), rawnode.go:356 (m.Index).
// Assumes: m is owned (a message the caller built or a Ready handed out whole).
// Specs: msgPts_unfold.spec, Message.GetTo.spec, Message.GetTerm.spec.
func ReqFieldWrite(m *pb.Message, lead uint64) {
	term := m.GetTerm()
	m.To = new(lead)
	if m.GetTo() != lead || m.GetTerm() != term {
		panic("field write")
	}
}

// REQ raftpb/msgapp-indexes: a MsgApp's entries are numbered from its Index + 1 (raft's
// maybeAppend reads each entry's Index: findConflict, append's first index).
// Users: raft.go:1809 (logSliceFromMsgApp), log.go (maybeAppend, findConflict).
// Assumes: m is a MsgApp raft sent (msgPts, R1's msgSent).
// Specs: Message.GetEntries.spec, msgEnts_app.spec, Entry.GetIndex.spec.
func ReqMsgAppIndexes(m *pb.Message) {
	if m.GetType() != pb.MsgApp {
		return
	}
	for j, e := range m.GetEntries() {
		if e.GetIndex() != m.GetIndex()+1+uint64(j) {
			panic("entry index")
		}
	}
}

// REQ raftpb/clone-message: a clone of a message holds the same fields (the examples' in-process
// transport steps a copy; rafthttp's link heartbeat is cloned).
// Users: examples' copyMsg, rafthttp stream.go (linkHeartbeatMessage).
// Specs: proto's Clone.spec, msgPts_msgAt.spec, the getters.
func ReqCloneMessage(m *pb.Message) *pb.Message {
	c := proto.Clone(m).(*pb.Message)
	if c.GetType() != m.GetType() || c.GetIndex() != m.GetIndex() || len(c.GetEntries()) != len(m.GetEntries()) {
		panic("clone differs")
	}
	return c
}

// REQ raftpb/wire-roundtrip: a message marshaled by the sender decodes, at the receiver, to the
// same fields (rafthttp's pipeline and stream).
// Users: rafthttp msg_codec.go:40 (encode), http.go:139 (decode).
// Assumes: m is a message raft sent whose size fits (msgPts, Msg.wireBound < 2^48).
// Specs: proto's Marshal.spec and Unmarshal.spec, msgPts_msgAt.spec, wire_fun.spec.
func ReqWireRoundTrip(m *pb.Message) *pb.Message {
	bs, err := proto.Marshal(m)
	if err != nil {
		panic("raftpb marshals")
	}
	var r pb.Message
	if err := proto.Unmarshal(bs, &r); err != nil {
		panic("decode of an encoding")
	}
	if r.GetType() != m.GetType() || r.GetTerm() != m.GetTerm() || r.GetCommit() != m.GetCommit() {
		panic("wire changed the message")
	}
	return &r
}
