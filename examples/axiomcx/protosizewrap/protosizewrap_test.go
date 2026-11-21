// Package protosizewrap is the Go counterexample to the post `0 <= n` of the trust-boundary
// axioms proto.SizeMessage.wp_proof (Spec/google_golang_org/protobuf/proto/SizeMessage.lean) and,
// until 2026-11-20, proto.Size.wp_proof at a range response and at a read-only transaction's
// response (Spec/google_golang_org/protobuf/proto/Size.lean); notes/axiom-review/proto-size-wrap.md.
//
// protobuf-go v1.36.12 sums a message's size with Go's wrapping int additions
// (internal/impl/encode.go, codec_field.go): a message whose repeated message fields hold the same
// pointer many times, each time counted, has a true size above 2^63 in little memory, and
// proto.Size returns a negative int. The premises admit such messages: raft's msgPtsC holds the
// entries read-only (entRO, persistent: shared pointers allowed) and says nothing of the
// responses' contents; txn.rangeResponseIs's key-values (kvsIs) and txn.roTxnRespRd's responses
// are read-only too. The large byte slices are made but never touched (Size reads only their
// lengths), so they cost address space, not memory.
//
// Heavy (each test 20-35 s; TestSizeRangeResponseNegative fills an 8 GiB slice): run with
// PROTOSIZEWRAP=1. Tests only, no Goose project.
package protosizewrap

import (
	"os"
	"testing"

	pb "go.etcd.io/etcd/api/v3/etcdserverpb"
	"go.etcd.io/etcd/api/v3/mvccpb"
	raftpb "go.etcd.io/raft/v3/raftpb"
	"google.golang.org/protobuf/proto"
)

const (
	k = 1 << 15 // shared pointers per level
	d = 1 << 33 // bytes of the shared value (untouched)
)

func heavy(t *testing.T) {
	if os.Getenv("PROTOSIZEWRAP") == "" {
		t.Skip("set PROTOSIZEWRAP=1 to run (heavy)")
	}
}

func check(t *testing.T, what string, n int) {
	t.Logf("proto.Size(%s) = %d", what, n)
	if n >= 0 {
		t.Fatalf("proto.Size(%s) is not negative: not a counterexample", what)
	}
}

// proto.SizeMessage: a *raftpb.Message whose Responses hold one response k times, whose Entries
// hold one entry k times, with a 2^33-byte Data.
func TestSizeMessageNegative(t *testing.T) {
	heavy(t)
	e := &raftpb.Entry{Data: make([]byte, d)}
	r := &raftpb.Message{Entries: make([]*raftpb.Entry, k)}
	for i := range r.Entries {
		r.Entries[i] = e
	}
	m := &raftpb.Message{Responses: make([]*raftpb.Message, k)}
	for i := range m.Responses {
		m.Responses[i] = r
	}
	check(t, "message", proto.Size(m))
}

// proto.Size at a range response (txn.rangeResponseIs): one key-value 2^30 times.
func TestSizeRangeResponseNegative(t *testing.T) {
	heavy(t)
	kv := &mvccpb.KeyValue{Value: make([]byte, d)}
	kvs := make([]*mvccpb.KeyValue, 1<<30)
	for i := range kvs {
		kvs[i] = kv
	}
	check(t, "range response", proto.Size(&pb.RangeResponse{Header: &pb.ResponseHeader{}, Kvs: kvs}))
}

// proto.Size at a read-only transaction's response (txn.roTxnRespRd): one range response k times,
// holding one key-value k times.
func TestSizeTxnResponseNegative(t *testing.T) {
	heavy(t)
	kv := &mvccpb.KeyValue{Value: make([]byte, d)}
	rr := &pb.RangeResponse{Header: &pb.ResponseHeader{}, Kvs: make([]*mvccpb.KeyValue, k)}
	for i := range rr.Kvs {
		rr.Kvs[i] = kv
	}
	op := &pb.ResponseOp{Response: &pb.ResponseOp_ResponseRange{ResponseRange: rr}}
	r := &pb.TxnResponse{Header: &pb.ResponseHeader{}, Responses: make([]*pb.ResponseOp, k)}
	for i := range r.Responses {
		r.Responses[i] = op
	}
	check(t, "txn response", proto.Size(r))
}
