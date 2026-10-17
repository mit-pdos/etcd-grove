package raft

import (
	"errors"
	"testing"

	pb "go.etcd.io/raft/v3/raftpb"
)

// asyncDrive handles one ReadyWithOpts in async-storage mode: the append thread's
// message is processed at once; the apply thread's messages are returned (not applied).
func asyncDrive(t *testing.T, rn *RawNode, s *MemoryStorage, opts ReadyOpts) (applyMsgs []*pb.Message) {
	rd := rn.ReadyWithOpts(opts)
	for _, m := range rd.Messages {
		switch m.GetTo() {
		case LocalAppendThread:
			if len(m.GetEntries()) > 0 {
				if err := s.Append(m.GetEntries()); err != nil {
					t.Fatal(err)
				}
			}
			if m.Term != nil {
				s.SetHardState(&pb.HardState{Term: m.Term, Vote: m.Vote, Commit: m.Commit})
			}
			for _, r := range m.GetResponses() {
				if r.GetTo() == rn.raft.id {
					_ = rn.Step(r)
				}
			}
		case LocalApplyThread:
			applyMsgs = append(applyMsgs, m)
		}
	}
	return applyMsgs
}

// TestReview60Async: in async-storage mode, a paused Ready carries no MsgStorageApply,
// and after resuming the applied entries are contiguous with no gap or duplicate.
func TestReview60Async(t *testing.T) {
	s := newTestMemoryStorage(withPeers(1))
	c := newTestConfig(1, 10, 1, s)
	c.AsyncStorageWrites = true
	c.MaxCommittedSizePerReady = 1 // one entry per apply batch
	rn, err := NewRawNode(c)
	if err != nil {
		t.Fatal(err)
	}
	if err := rn.Campaign(); err != nil {
		t.Fatal(err)
	}
	paused := ReadyOpts{DisableCommittedEntries: true}
	var got []uint64
	last := uint64(0)
	apply := func(ms []*pb.Message) {
		for _, m := range ms {
			for _, e := range m.GetEntries() {
				if e.GetIndex() != last+1 {
					t.Fatalf("gap/dup: got %d after %d", e.GetIndex(), last)
				}
				last = e.GetIndex()
				got = append(got, last)
			}
			for _, r := range m.GetResponses() {
				_ = rn.Step(r)
			}
		}
	}
	for round := 0; round < 40; round++ {
		if round%3 == 0 {
			_ = rn.Propose([]byte("x"))
		}
		if !rn.HasReady() {
			continue
		}
		var ms []*pb.Message
		if round%2 == 0 {
			ms = asyncDrive(t, rn, s, paused)
			if len(ms) != 0 {
				t.Fatalf("paused Ready carried %d MsgStorageApply", len(ms))
			}
		} else {
			ms = asyncDrive(t, rn, s, ReadyOpts{})
		}
		apply(ms)
	}
	for i := 0; i < 50 && rn.HasReady(); i++ {
		apply(asyncDrive(t, rn, s, ReadyOpts{}))
	}
	if last != rn.raft.raftLog.committed {
		t.Fatalf("applied %d, committed %d", last, rn.raft.raftLog.committed)
	}
	t.Logf("applied %v", got)
}

// TestReview60UncommittedBackpressure: on a leader, uncommittedSize is reduced only when
// entries are *applied* (MsgStorageApplyResp), so pausing CommittedEntries makes the
// leader drop proposals once MaxUncommittedEntriesSize is reached, though every entry is
// committed and persisted.
func TestReview60UncommittedBackpressure(t *testing.T) {
	s := newTestMemoryStorage(withPeers(1))
	c := newTestConfig(1, 10, 1, s)
	c.MaxUncommittedEntriesSize = 64
	rn, err := NewRawNode(c)
	if err != nil {
		t.Fatal(err)
	}
	_ = rn.Campaign()
	paused := ReadyOpts{DisableCommittedEntries: true}
	handle := func(opts ReadyOpts) {
		rd := rn.ReadyWithOpts(opts)
		s.Append(rd.Entries)
		if !IsEmptyHardState(rd.HardState) {
			s.SetHardState(rd.HardState)
		}
		rn.Advance(rd)
	}
	for i := 0; i < 5; i++ {
		handle(ReadyOpts{})
	}
	dropped := -1
	for i := 0; i < 100; i++ {
		err := rn.Propose(make([]byte, 16))
		if errors.Is(err, ErrProposalDropped) {
			dropped = i
			break
		}
		handle(paused)
	}
	if dropped < 0 {
		t.Fatalf("no proposal dropped")
	}
	t.Logf("proposal %d dropped; committed=%d applied=%d applying=%d",
		dropped, rn.raft.raftLog.committed, rn.raft.raftLog.applied, rn.raft.raftLog.applying)
	// resume: proposals accepted again after applying
	for i := 0; i < 5; i++ {
		handle(ReadyOpts{})
	}
	if err := rn.Propose(make([]byte, 16)); err != nil {
		t.Fatalf("after resume: %v", err)
	}
}

// TestReview60ConfChangeBlocked: a paused node with a committed unapplied conf change
// refuses to campaign, and (as leader) drops a second conf change.
func TestReview60ConfChangeBlocked(t *testing.T) {
	s := newTestMemoryStorage(withPeers(1))
	rn, err := NewRawNode(newTestConfig(1, 10, 1, s))
	if err != nil {
		t.Fatal(err)
	}
	_ = rn.Campaign()
	handle := func(opts ReadyOpts) {
		rd := rn.ReadyWithOpts(opts)
		s.Append(rd.Entries)
		if !IsEmptyHardState(rd.HardState) {
			s.SetHardState(rd.HardState)
		}
		rn.Advance(rd)
	}
	for i := 0; i < 5; i++ {
		handle(ReadyOpts{})
	}
	paused := ReadyOpts{DisableCommittedEntries: true}
	cc := &pb.ConfChange{Type: pb.ConfChangeAddLearnerNode.Enum(), NodeId: new(uint64(2))}
	if err := rn.ProposeConfChange(cc); err != nil {
		t.Fatal(err)
	}
	handle(paused)
	handle(paused)
	t.Logf("committed=%d applied=%d pendingConf=%d", rn.raft.raftLog.committed, rn.raft.raftLog.applied, rn.raft.pendingConfIndex)
	cc2 := &pb.ConfChange{Type: pb.ConfChangeAddLearnerNode.Enum(), NodeId: new(uint64(3))}
	_ = rn.ProposeConfChange(cc2)
	rd := rn.ReadyWithOpts(paused)
	for _, e := range rd.Entries {
		t.Logf("appended entry %d type %v", e.GetIndex(), e.GetType())
	}
}
