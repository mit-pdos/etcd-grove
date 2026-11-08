//go:build with_tla

package tracecheck

import (
	"bytes"
	"strings"
	"testing"

	pb "go.etcd.io/raft/v3/raftpb"
)

// Witnesses of places where etcdraft.tla does not fit raft (notes/raft-trace-validation.md, "Where
// etcdraft.tla does not fit raft"), each a schedule of the deterministic driver whose trace the
// checker rejects (TLC on raft's Traceetcdraft.tla rejects the same traces at the same lines,
// 2026-11-08). Found by the reviews of trace-check's Draft S4 (notes/trace-validation-reviews/).
// Each asserts the rejection: a test that starts passing means the gap is gone (or the driver no
// longer reaches it).

// rejected checks that the trace of s is rejected, at line wantLine, by the invariant
// wantViolation if not empty (else as unmatched).
func rejected(t *testing.T, s *Sim, wantLine int, wantViolation string) {
	t.Helper()
	var buf bytes.Buffer
	if err := WriteNDJSON(&buf, s.Events()); err != nil {
		t.Fatal(err)
	}
	r, _, err := goVerdicts(t, buf.Bytes())
	if err != nil {
		t.Fatal(err)
	}
	switch {
	case wantViolation != "":
		if r.Violation != wantViolation || r.ViolLine != wantLine {
			t.Fatalf("want %s violated at line %d, got %+v", wantViolation, wantLine, r)
		}
	case r.OK || r.Line != wantLine || !strings.Contains(r.String(), "not matched"):
		t.Fatalf("want not matched at line %d, got %v", wantLine, r)
	}
}

// Five voters: node 5 learns leader 1 of term 2 from a heartbeat without having voted, then gets
// candidate 2's MsgVote of term 2: raft rejects (lead != None), etcdraft.tla grants.
func TestGap6FiveVoters(t *testing.T) {
	s, err := New(Config{Nodes: 5})
	if err != nil {
		t.Fatal(err)
	}
	for _, n := range s.nodes {
		if err := s.ready(n); err != nil {
			t.Fatal(err)
		}
	}
	take := func(from, to uint64, typ pb.MessageType) {
		for k, m := range s.inflight {
			if m.GetFrom() == from && m.GetTo() == to && m.GetType() == typ {
				s.inflight = append(s.inflight[:k], s.inflight[k+1:]...)
				_ = s.node(to).rn.Step(m)
				return
			}
		}
		t.Fatalf("no %v %d->%d in flight", typ, from, to)
	}
	rd := func(id uint64) {
		if err := s.ready(s.node(id)); err != nil {
			t.Fatal(err)
		}
	}
	_ = s.node(1).rn.Campaign()
	_ = s.node(2).rn.Campaign()
	rd(1)
	rd(2)
	take(1, 3, pb.MsgVote)
	take(1, 4, pb.MsgVote)
	rd(3)
	rd(4)
	take(3, 1, pb.MsgVoteResp)
	take(4, 1, pb.MsgVoteResp)
	rd(1)
	s.node(1).rn.Tick()
	rd(1)
	take(1, 5, pb.MsgHeartbeat)
	rd(5)
	take(2, 5, pb.MsgVote)
	rd(5)
	take(5, 2, pb.MsgVoteResp)
	rejected(t, s, 124, "")
}

// Three voters. Node 1 wins term 2 with node 2's vote; its MsgVote to node 3 is delayed past its
// first heartbeat, so node 3 learns leader 1 of term 2 without voting, then gets node 1's own
// MsgVote of term 2: raft rejects (lead != None), etcdraft.tla grants (votedFor = Nil).
func TestGap6ThreeVoters(t *testing.T) {
	s, err := New(Config{Nodes: 3})
	if err != nil {
		t.Fatal(err)
	}
	rd := func(id uint64) {
		if err := s.ready(s.node(id)); err != nil {
			t.Fatal(err)
		}
	}
	for id := uint64(1); id <= 3; id++ {
		rd(id)
	}
	take := func(from, to uint64, typ pb.MessageType) {
		for k, m := range s.inflight {
			if m.GetFrom() == from && m.GetTo() == to && m.GetType() == typ {
				s.inflight = append(s.inflight[:k], s.inflight[k+1:]...)
				_ = s.node(to).rn.Step(m)
				return
			}
		}
		t.Fatalf("no %v %d->%d in flight", typ, from, to)
	}
	_ = s.node(1).rn.Campaign()
	rd(1)
	take(1, 2, pb.MsgVote)
	rd(2)
	take(2, 1, pb.MsgVoteResp) // node 1 leader of term 2
	rd(1)                      // MsgApps (held)
	s.node(1).rn.Tick()        // heartbeats
	rd(1)
	take(1, 3, pb.MsgHeartbeat) // node 3: term 2, lead 1, no vote
	rd(3)
	take(1, 3, pb.MsgVote) // the delayed MsgVote of term 2
	rd(3)
	take(3, 1, pb.MsgVoteResp)
	rd(1)
	rejected(t, s, 63, "")
}

// Three voters. Node 1 leads term 2 and appends its empty entry at 4 (term 2), which reaches no
// one. Node 2 leads term 3 (node 3's vote), appends its empty entry at 4 (term 3), which reaches
// no one, and stays leader of 3 (no check-quorum). Node 1 leads term 4 (node 3's vote) and
// commits index 5, so index 4 (term 2) is committed, which leader 2 (term 3 > 2) lacks:
// LeaderCompletenessInv.
func TestGap7LeaderCompleteness(t *testing.T) {
	s, err := New(Config{Nodes: 3})
	if err != nil {
		t.Fatal(err)
	}
	rd := func(id uint64) {
		if err := s.ready(s.node(id)); err != nil {
			t.Fatal(err)
		}
	}
	for id := uint64(1); id <= 3; id++ {
		rd(id)
	}
	take := func(from, to uint64, typ pb.MessageType) {
		for k, m := range s.inflight {
			if m.GetFrom() == from && m.GetTo() == to && m.GetType() == typ {
				s.inflight = append(s.inflight[:k], s.inflight[k+1:]...)
				_ = s.node(to).rn.Step(m)
				return
			}
		}
		t.Fatalf("no %v %d->%d in flight", typ, from, to)
	}
	drop := func() { s.inflight = nil }
	// term 2: node 1
	_ = s.node(1).rn.Campaign()
	rd(1)
	take(1, 2, pb.MsgVote)
	take(1, 3, pb.MsgVote)
	rd(2)
	rd(3)
	take(2, 1, pb.MsgVoteResp)
	take(3, 1, pb.MsgVoteResp)
	rd(1) // MsgApps of the empty entry at 4 (term 2)
	drop()
	// term 3: node 2
	_ = s.node(2).rn.Campaign()
	rd(2)
	take(2, 1, pb.MsgVote)
	take(2, 3, pb.MsgVote)
	rd(1)
	rd(3)
	take(3, 2, pb.MsgVoteResp)
	drop()
	rd(2) // node 2 leader of 3, empty entry at 4 (term 3)
	drop()
	// term 4: node 1
	_ = s.node(1).rn.Campaign()
	rd(1)
	take(1, 3, pb.MsgVote)
	drop()
	rd(3)
	take(3, 1, pb.MsgVoteResp)
	rd(1)
	take(1, 3, pb.MsgApp) // prev 4 (term 2): rejected
	drop()
	rd(3)
	take(3, 1, pb.MsgAppResp)
	rd(1)
	take(1, 3, pb.MsgApp) // prev 3, entries 4, 5
	drop()
	rd(3)
	take(3, 1, pb.MsgAppResp) // commit 5
	rd(1)
	rejected(t, s, 110, "LeaderCompletenessInv")
}
