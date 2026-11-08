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
// Upstream's etcdraft.tla rejected each; the corrected specification (etc/tla-fixes, 2026-11-08)
// the checker transcribes accepts each, so each now asserts the acceptance (and still checks the
// driver reached the schedule). `rejected` stays for witnesses of gaps still open.

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
	accepted(t, s) // upstream: not matched at line 124 (fixed: raft's lead, etc/tla-fixes 0006)
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
	accepted(t, s) // upstream: not matched at line 63 (fixed: raft's lead, etc/tla-fixes 0006)
}

// Three voters. Node 1 leads term 2 and appends its empty entry at 4 (term 2), which reaches no
// one. Node 2 leads term 3 (node 3's vote), appends its empty entry at 4 (term 3), which reaches
// no one, and stays leader of 3 (no check-quorum). Node 1 leads term 4 (node 3's vote) and
// commits index 5, so index 4 (term 2) is committed, which leader 2 (term 3 > 2) lacks: upstream's
// LeaderCompletenessInv fails (TLC on raft's own tla/, and this checker before the repair, reject at
// line 110). The checker's repaired invariant (Q4 (b), the leader's term at least the committing
// server's: 3 < 4) accepts it: the trace now passes, and the stale leader is still there.
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
	if l := s.Leaders(); len(l) != 2 {
		t.Fatalf("leaders %v, want the stale leader 2 and leader 1", l)
	}
	accepted(t, s)
}

// accepted: the direct checker matches the whole trace and finds no invariant violated.
func accepted(t *testing.T, s *Sim) {
	t.Helper()
	var buf bytes.Buffer
	if err := WriteNDJSON(&buf, s.Events()); err != nil {
		t.Fatal(err)
	}
	r, _, err := goVerdicts(t, buf.Bytes())
	if err != nil {
		t.Fatal(err)
	}
	if !r.TLCOK() {
		t.Fatalf("want accepted, got %v", r)
	}
}

// Five voters, MaxSizePerMsg cutting every batch to one entry. Node 1 leads term 2, its entry x
// at 4 (term 2) reaches node 3 only. Node 2 leads term 3 (votes 4, 5), its entry y at 4 (term 3)
// reaches node 4. Node 1 leads term 4 (votes 3, 5), appends z at 5; node 5 gets x alone (cut
// batch), acks 4; z reaches 3 and 4, so 5 is committed (term 4) and with it x. A heartbeat gives
// node 5 commit min(Match 4, 5) = 4: node 5's log ends at x (term 2) with x committed, while
// node 2's log ends at y (term 3): MoreUpToDateCorrectInv(2, 5) is violated, no leader stale.
func TestGap8MoreUpToDate(t *testing.T) {
	s, err := New(Config{Nodes: 5, MaxSizePerMsg: 1})
	if err != nil {
		t.Fatal(err)
	}
	rd := func(id uint64) {
		if err := s.ready(s.node(id)); err != nil {
			t.Fatal(err)
		}
	}
	for k := 0; k < 8; k++ {
		for id := uint64(1); id <= 5; id++ {
			rd(id)
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
	drop := func() { s.inflight = nil }
	// term 2: node 1 (votes 4, 5; node 3 joins term 2)
	err = s.node(1).rn.Campaign()
	st := s.node(1).rn.BasicStatus()
	t.Logf("campaign err %v state %v term %d applied %d commit %d", err, st.RaftState, st.HardState.GetTerm(), st.Applied, st.HardState.GetCommit())
	rd(1)
	for _, m := range s.inflight {
		t.Logf("inflight %v %d->%d", m.GetType(), m.GetFrom(), m.GetTo())
	}
	take(1, 2, pb.MsgVote)
	take(1, 3, pb.MsgVote)
	take(1, 4, pb.MsgVote)
	take(1, 5, pb.MsgVote)
	drop()
	rd(2)
	rd(3)
	rd(4)
	rd(5)
	take(4, 1, pb.MsgVoteResp)
	take(5, 1, pb.MsgVoteResp)
	drop()
	rd(1) // x at 4 (term 2)
	take(1, 3, pb.MsgApp)
	drop()
	rd(3)
	drop()
	// term 3: node 2 (votes 4, 5); node 1 steps down
	_ = s.node(2).rn.Campaign()
	rd(2)
	take(2, 1, pb.MsgVote)
	take(2, 4, pb.MsgVote)
	take(2, 5, pb.MsgVote)
	drop()
	rd(1)
	rd(4)
	rd(5)
	take(4, 2, pb.MsgVoteResp)
	take(5, 2, pb.MsgVoteResp)
	drop()
	rd(2) // y at 4 (term 3)
	take(2, 4, pb.MsgApp)
	drop()
	rd(4)
	drop()
	// term 4: node 1 (votes 3, 5); nodes 2, 4 refuse and follow term 4
	_ = s.node(1).rn.Campaign()
	rd(1)
	take(1, 2, pb.MsgVote)
	take(1, 3, pb.MsgVote)
	take(1, 4, pb.MsgVote)
	take(1, 5, pb.MsgVote)
	drop()
	rd(2)
	rd(3)
	rd(4)
	rd(5)
	take(3, 1, pb.MsgVoteResp)
	take(5, 1, pb.MsgVoteResp)
	drop()
	rd(1) // z at 5 (term 4)
	take(1, 3, pb.MsgApp)
	take(1, 4, pb.MsgApp)
	take(1, 5, pb.MsgApp)
	drop()
	rd(3)
	rd(4)
	rd(5)
	take(3, 1, pb.MsgAppResp)
	take(4, 1, pb.MsgAppResp)
	take(5, 1, pb.MsgAppResp)
	drop()
	rd(1) // [x] to 4 and 5 (cut)
	take(1, 4, pb.MsgApp)
	take(1, 5, pb.MsgApp)
	drop()
	rd(4)
	rd(5)
	take(4, 1, pb.MsgAppResp)
	take(5, 1, pb.MsgAppResp)
	drop()
	rd(1) // [z] to 4 and 5
	take(1, 4, pb.MsgApp)
	drop()
	rd(4)
	take(4, 1, pb.MsgAppResp) // 5 committed
	drop()
	rd(1)
	drop()
	s.node(1).rn.Tick() // heartbeats
	rd(1)
	take(1, 5, pb.MsgHeartbeat)
	rd(5)
	drop()
	r := s.Events()
	t.Logf("events %d", len(r))
	accepted(t, s) // upstream: MoreUpToDateCorrectInv violated at line 249 (not checked, etc/tla-fixes 0009)
}
