package raft

import (
	"testing"

	pb "go.etcd.io/raft/v3/raftpb"
)

// newReadyOptsNode returns a single-voter RawNode that is leader and has committed
// entries waiting to be applied (none handed out yet).
func newReadyOptsNode(t *testing.T) (*RawNode, *MemoryStorage) {
	s := newTestMemoryStorage(withPeers(1))
	rn, err := NewRawNode(newTestConfig(1, 10, 1, s))
	if err != nil {
		t.Fatal(err)
	}
	if err := rn.Campaign(); err != nil {
		t.Fatal(err)
	}
	// Persist everything, but do not apply committed entries yet.
	for i := 0; i < 10 && rn.HasReady(); i++ {
		rd := rn.ReadyWithOpts(ReadyOpts{DisableCommittedEntries: true})
		s.Append(rd.Entries)
		if !IsEmptyHardState(rd.HardState) {
			s.SetHardState(rd.HardState)
		}
		rn.Advance(rd)
	}
	for i := 0; i < 3; i++ {
		if err := rn.Propose([]byte("x")); err != nil {
			t.Fatal(err)
		}
		rd := rn.ReadyWithOpts(ReadyOpts{DisableCommittedEntries: true})
		s.Append(rd.Entries)
		if !IsEmptyHardState(rd.HardState) {
			s.SetHardState(rd.HardState)
		}
		rn.Advance(rd)
	}
	return rn, s
}

// TestReadyOptsHasReadyIgnoresOpts shows that HasReady keeps reporting a Ready while the
// only pending work is committed entries the caller paused with DisableCommittedEntries:
// a `for rn.HasReady() { rd := rn.ReadyWithOpts(paused); ...; rn.Advance(rd) }` loop
// never ends, each Ready empty.
func TestReadyOptsHasReadyIgnoresOpts(t *testing.T) {
	rn, s := newReadyOptsNode(t)
	paused := ReadyOpts{DisableCommittedEntries: true}
	empty := 0
	for i := 0; i < 100 && rn.HasReady(); i++ {
		rd := rn.ReadyWithOpts(paused)
		if len(rd.CommittedEntries) != 0 {
			t.Fatalf("committed entries handed out while disabled: %v", rd.CommittedEntries)
		}
		s.Append(rd.Entries)
		if len(rd.Entries) == 0 && len(rd.Messages) == 0 && IsEmptyHardState(rd.HardState) && rd.SoftState == nil {
			empty++
		}
		rn.Advance(rd)
	}
	if rn.HasReady() {
		t.Logf("HasReady still true after 100 paused Readys (%d of them empty): it ignores "+
			"DisableCommittedEntries", empty)
	} else {
		t.Fatalf("HasReady became false")
	}
}

// TestReadyOptsNoGapNoDup checks the property the proof states: pausing then resuming
// hands out every committed entry exactly once, in order.
func TestReadyOptsNoGapNoDup(t *testing.T) {
	rn, s := newReadyOptsNode(t)
	var applied []pb.Entry
	for i := 0; i < 20; i++ {
		opts := ReadyOpts{DisableCommittedEntries: i%2 == 0}
		if err := rn.Propose([]byte("y")); err != nil {
			t.Fatal(err)
		}
		rd := rn.ReadyWithOpts(opts)
		if opts.DisableCommittedEntries && len(rd.CommittedEntries) != 0 {
			t.Fatalf("committed entries while disabled")
		}
		s.Append(rd.Entries)
		if !IsEmptyHardState(rd.HardState) {
			s.SetHardState(rd.HardState)
		}
		applied = append(applied, rd.CommittedEntries...)
		rn.Advance(rd)
	}
	for rn.HasReady() {
		rd := rn.Ready()
		s.Append(rd.Entries)
		applied = append(applied, rd.CommittedEntries...)
		rn.Advance(rd)
	}
	for i, e := range applied {
		if e.Index != uint64(i+1) {
			t.Fatalf("entry %d has index %d", i, e.Index)
		}
	}
	last, _ := s.LastIndex()
	if uint64(len(applied)) != last {
		t.Fatalf("applied %d entries, log has %d", len(applied), last)
	}
}
