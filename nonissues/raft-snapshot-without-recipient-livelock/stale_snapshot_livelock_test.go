package raft

import (
	"testing"

	pb "go.etcd.io/raft/v3/raftpb"
	"google.golang.org/protobuf/proto"
)

// TestStaleSnapshotLivelock: a one-voter cluster on a MemoryStorage takes a snapshot and compacts
// its log, then adds a second voter. The newcomer needs the log from index 1, which is compacted
// away, so the leader sends it its storage's latest snapshot -- taken before the newcomer was
// added, so without it in its configuration -- and the newcomer drops it (restore: "recipient is
// not in the config"). The leader sends it again, forever, and with two voters nothing commits
// without the newcomer: the cluster is stuck. The control run takes a snapshot right after the
// change is applied, and the newcomer catches up.
func TestStaleSnapshotLivelock(t *testing.T) {
	if stuck := staleSnapshotRun(t, true); stuck {
		t.Fatalf("control (snapshot after the conf change): stuck")
	}
	if stuck := staleSnapshotRun(t, false); stuck {
		t.Errorf("the newcomer never caught up and the proposal never committed")
	}
}

// staleSnapshotRun runs the scenario of TestStaleSnapshotLivelock and says whether the cluster
// is stuck: the newcomer applied nothing, and a proposal made after the change did not commit.
func staleSnapshotRun(t *testing.T, fixSnapshot bool) bool {
	newNode := func(id uint64, st *MemoryStorage) *RawNode {
		rn, err := NewRawNode(&Config{ID: id, ElectionTick: 10, HeartbeatTick: 1,
			Storage: st, MaxSizePerMsg: 1 << 20, MaxInflightMsgs: 256, Logger: discardLogger})
		if err != nil {
			t.Fatal(err)
		}
		return rn
	}
	st1 := NewMemoryStorage()
	n1 := newNode(1, st1)
	if err := n1.Bootstrap([]Peer{{ID: 1}}); err != nil {
		t.Fatal(err)
	}
	st2 := NewMemoryStorage()
	nodes := map[uint64]*RawNode{1: n1}
	storages := map[uint64]*MemoryStorage{1: st1, 2: st2}
	var cs *pb.ConfState
	var applied uint64
	snapTaken := uint64(0)
	var inbox []*pb.Message
	// step handles every node's Ready once, as an application does, and routes the messages.
	step := func() {
		for id, rn := range nodes {
			if !rn.HasReady() {
				continue
			}
			rd := rn.Ready()
			st := storages[id]
			if !IsEmptySnap(rd.Snapshot) {
				st.ApplySnapshot(rd.Snapshot)
			}
			if !IsEmptyHardState(rd.HardState) {
				st.SetHardState(rd.HardState)
			}
			st.Append(rd.Entries)
			for _, m := range rd.Messages {
				inbox = append(inbox, proto.Clone(m).(*pb.Message))
			}
			for _, e := range rd.CommittedEntries {
				if e.GetType() == pb.EntryConfChange {
					var cc pb.ConfChange
					proto.Unmarshal(e.GetData(), &cc)
					s := rn.ApplyConfChange(&cc)
					if id == 1 {
						cs = s
						if fixSnapshot {
							st.CreateSnapshot(e.GetIndex(), cs, nil)
						}
					}
				}
				if id == 1 {
					applied = e.GetIndex()
				}
			}
			rn.Advance(rd)
		}
		ms := inbox
		inbox = nil
		for _, m := range ms {
			if rn, ok := nodes[m.GetTo()]; ok {
				rn.Step(m)
				if m.GetType() == pb.MsgSnap {
					nodes[m.GetFrom()].ReportSnapshot(m.GetTo(), SnapshotFinish)
				}
			}
		}
	}
	// the bootstrap's configuration takes effect once applied: then node 1 can campaign
	step()
	n1.Campaign()
	for i := 0; i < 10; i++ {
		step()
	}
	for i := 0; i < 10; i++ {
		n1.Propose([]byte("x"))
		step()
	}
	// a snapshot of everything applied, and the log compacted up to it
	if _, err := st1.CreateSnapshot(applied, cs, nil); err != nil {
		t.Fatal(err)
	}
	if err := st1.Compact(applied); err != nil {
		t.Fatal(err)
	}
	snapTaken = applied
	nodes[2] = newNode(2, st2)
	n1.ProposeConfChange(&pb.ConfChange{Type: pb.ConfChangeAddNode.Enum(), NodeId: new(uint64(2))})
	for i := 0; i < 20; i++ {
		step()
	}
	n1.Propose([]byte("after"))
	before := applied
	for i := 0; i < 200; i++ {
		n1.Tick()
		nodes[2].Tick()
		step()
	}
	newcomer := nodes[2].Status().Applied
	t.Logf("fixSnapshot=%v: snapshot at %d, leader applied %d -> %d, newcomer applied %d",
		fixSnapshot, snapTaken, before, applied, newcomer)
	return newcomer == 0 && applied == before
}
