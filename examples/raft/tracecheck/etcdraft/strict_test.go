package etcdraft

import "testing"

// The search branching is detected (TLC's TraceMatched fails then): node 1, the leader, receives a
// heartbeat response from node 2 that two messages in transit match, differing only in their
// mmatchIndex (which LoglineIsAppendEntriesResponse does not check of a heartbeat's), so the two
// receipts give two states.
func TestBranchingDetected(t *testing.T) {
	line := func(nid, name string, msg *EventMsg) Event {
		return Event{Name: name, NID: nid, State: EventState{Term: 1, Vote: "0", Commit: 0}, Role: "StateFollower",
			Log: 0, Conf: [2][]string{{"1", "2"}, {}}, Msg: msg}
	}
	events := []Event{line("1", "InitState", nil), line("2", "InitState", nil),
		line("1", "ReceiveAppendEntriesResponse", &EventMsg{Type: "MsgHeartbeatResp", Term: 1, From: "2", To: "1", Vote: "0"})}
	tr, err := NewTrace(events)
	if err != nil {
		t.Fatal(err)
	}
	s := tr.Init().S.clone()
	s.mut(1).State = Leader
	for _, match := range []int{0, 5} {
		s.Messages = s.Messages.With(&Msg{Type: AppendEntriesResponse, Subtype: "heartbeat", Term: 1, Success: true,
			MatchIndex: match, Source: 2, Dest: 1})
	}
	succ, info := tr.StepLine(TState{S: s, L: 3, PL: 3}, false)
	if len(succ) != 2 || !info.Branched {
		t.Fatalf("want two successors and a branch, got %d, branched %t", len(succ), info.Branched)
	}
}
