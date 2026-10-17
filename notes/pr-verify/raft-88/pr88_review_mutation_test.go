package raft

import (
	"testing"

	pb "go.etcd.io/raft/v3/raftpb"
)

// TestPR88CallbackMutationLeaks: the callback receives pb.Message by value, which suggests it
// cannot affect the proposal; but Entries shares its backing array (and each entry's Data its
// bytes) with the message raft forwards. A callback that edits an entry and returns false has
// changed the proposal the leader will append. Scalar edits (m.Type, m.To) are lost, entry edits
// are not; the Config doc says nothing about either.
func TestPR88CallbackMutationLeaks(t *testing.T) {
	cfg := newTestConfig(2, 10, 1, newTestMemoryStorage(withPeers(1, 2)))
	cfg.DisableProposalForwardingCallback = func(m pb.Message) bool {
		m.Entries[0].Data = []byte("mutated") // entry slot shared with the caller's slice
		m.Entries[1].Data[0] = 'X'            // bytes shared too
		m.Type = pb.MsgApp                    // lost: by-value copy
		return false
	}
	r := newRaft(cfg)
	r.becomeFollower(1, 1)
	ents := []pb.Entry{{Data: []byte("orig")}, {Data: []byte("abc")}}
	if err := r.Step(pb.Message{From: 2, To: 2, Type: pb.MsgProp, Entries: ents}); err != nil {
		t.Fatal(err)
	}
	if len(r.msgs) != 1 {
		t.Fatalf("expected 1 forwarded msg, got %d", len(r.msgs))
	}
	fw := r.msgs[0]
	t.Logf("forwarded: type=%v to=%d ents=%q,%q", fw.Type, fw.To, fw.Entries[0].Data, fw.Entries[1].Data)
	if string(fw.Entries[0].Data) == "mutated" && string(fw.Entries[1].Data) == "Xbc" {
		t.Errorf("callback's edits to the entries reached the forwarded proposal (and the caller's slice: %q)", ents[0].Data)
	}
}
