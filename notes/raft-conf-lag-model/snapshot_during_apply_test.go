// Copyright 2026 The etcd Authors
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

package raft

// A snapshot restored while the application is still applying the previous Ready makes
// the application's ApplyConfChange calls for that Ready's conf changes apply them on top
// of the snapshot's configuration, which already reflects them (and later changes): the
// configuration in use is then neither the snapshot's nor any configuration of the log.
//
// The application follows doc.go (apply the committed entries, ApplyConfChange included,
// then Advance) and steps the messages it receives meanwhile, as node.run does: it serves
// recvc while it waits for Advance. Public RawNode API only.
//
// C0 = {1,2,3}; follower 2 receives C1 = "add 4" (index 1) committed and starts applying it.
// Meanwhile the leader (which compacted its log) sends a snapshot at index 3 whose ConfState,
// {1,2,3}, reflects C1 and a later C2 = "remove 4" (index 2). Node 2 restores it, then the
// application finishes applying C1: node 2's configuration becomes {1,2,3,4}.
//
// The test PASSES when the divergence is reproduced.

import (
	"testing"

	pb "go.etcd.io/raft/v3/raftpb"
)

func TestSnapshotDuringApplyStaleConfChange(t *testing.T) {
	st := NewMemoryStorage()
	if err := st.ApplySnapshot(pb.Snapshot{Metadata: pb.SnapshotMetadata{
		ConfState: pb.ConfState{Voters: []uint64{1, 2, 3}},
	}}); err != nil {
		t.Fatal(err)
	}
	rn, err := NewRawNode(&Config{
		ID: 2, ElectionTick: 10, HeartbeatTick: 1, Storage: st,
		MaxSizePerMsg: noLimit, MaxInflightMsgs: 256, Logger: discardLogger,
	})
	if err != nil {
		t.Fatal(err)
	}
	c1 := pb.ConfChange{Type: pb.ConfChangeAddNode, NodeId: 4}
	data, err := c1.Marshal()
	if err != nil {
		t.Fatal(err)
	}
	// The leader (node 1, term 1) replicates C1 at index 1 and commits it.
	if err := rn.Step(pb.Message{From: 1, To: 2, Term: 1, Type: pb.MsgApp, Index: 0, LogTerm: 0,
		Entries: []pb.Entry{{Term: 1, Index: 1, Type: pb.EntryConfChange, Data: data}}, Commit: 1}); err != nil {
		t.Fatal(err)
	}
	rd := rn.Ready()
	if len(rd.CommittedEntries) != 1 || rd.CommittedEntries[0].Type != pb.EntryConfChange {
		t.Fatalf("expected C1 committed, got %+v", rd.CommittedEntries)
	}
	if err := st.SetHardState(rd.HardState); err != nil {
		t.Fatal(err)
	}
	if err := st.Append(rd.Entries); err != nil {
		t.Fatal(err)
	}
	// The application is applying C1. Meanwhile a snapshot arrives (index 3, after
	// C2 = "remove 4" at index 2) and is stepped, as node.run does while it waits
	// for Advance.
	snap := pb.Snapshot{Metadata: pb.SnapshotMetadata{Index: 3, Term: 1,
		ConfState: pb.ConfState{Voters: []uint64{1, 2, 3}}}}
	if err := rn.Step(pb.Message{From: 1, To: 2, Term: 1, Type: pb.MsgSnap, Snapshot: &snap}); err != nil {
		t.Fatal(err)
	}
	t.Logf("after the snapshot: %v", rn.Status().Config)
	// The application finishes applying C1, then Advances (doc.go steps 3 and 4).
	cs := rn.ApplyConfChange(c1)
	rn.Advance(rd)
	// The next Ready carries the snapshot; the application applies it.
	rd = rn.Ready()
	if IsEmptySnap(rd.Snapshot) {
		t.Fatal("expected the snapshot in the next Ready")
	}
	if err := st.ApplySnapshot(rd.Snapshot); err != nil {
		t.Fatal(err)
	}
	rn.Advance(rd)
	got := rn.Status().Config.String()
	t.Logf("ApplyConfChange returned %v; configuration in use %s; snapshot's ConfState %v", cs, got, snap.Metadata.ConfState)
	if got == "voters=(1 2 3)" {
		t.Fatal("not reproduced: the configuration in use is the snapshot's")
	}
	t.Logf("DIVERGENCE reproduced: node 2 uses %s, the log's configuration at index 3 is voters=(1 2 3)", got)
}

// The same with joint consensus: C1 enters a joint configuration (index 1); the snapshot
// (index 2) was taken in that joint configuration. Applying C1 on top of it panics
// ("config is already joint").
func TestSnapshotDuringApplyStaleEnterJointPanics(t *testing.T) {
	st := NewMemoryStorage()
	if err := st.ApplySnapshot(pb.Snapshot{Metadata: pb.SnapshotMetadata{
		ConfState: pb.ConfState{Voters: []uint64{1, 2, 3}},
	}}); err != nil {
		t.Fatal(err)
	}
	rn, err := NewRawNode(&Config{
		ID: 2, ElectionTick: 10, HeartbeatTick: 1, Storage: st,
		MaxSizePerMsg: noLimit, MaxInflightMsgs: 256, Logger: discardLogger,
	})
	if err != nil {
		t.Fatal(err)
	}
	c1 := pb.ConfChangeV2{Transition: pb.ConfChangeTransitionJointExplicit,
		Changes: []pb.ConfChangeSingle{{Type: pb.ConfChangeAddNode, NodeId: 4}}}
	data, err := c1.Marshal()
	if err != nil {
		t.Fatal(err)
	}
	if err := rn.Step(pb.Message{From: 1, To: 2, Term: 1, Type: pb.MsgApp,
		Entries: []pb.Entry{{Term: 1, Index: 1, Type: pb.EntryConfChangeV2, Data: data}}, Commit: 1}); err != nil {
		t.Fatal(err)
	}
	rd := rn.Ready()
	if len(rd.CommittedEntries) != 1 {
		t.Fatalf("expected C1 committed, got %+v", rd.CommittedEntries)
	}
	if err := st.SetHardState(rd.HardState); err != nil {
		t.Fatal(err)
	}
	if err := st.Append(rd.Entries); err != nil {
		t.Fatal(err)
	}
	snap := pb.Snapshot{Metadata: pb.SnapshotMetadata{Index: 2, Term: 1,
		ConfState: pb.ConfState{Voters: []uint64{1, 2, 3, 4}, VotersOutgoing: []uint64{1, 2, 3}}}}
	if err := rn.Step(pb.Message{From: 1, To: 2, Term: 1, Type: pb.MsgSnap, Snapshot: &snap}); err != nil {
		t.Fatal(err)
	}
	t.Logf("after the snapshot: %v", rn.Status().Config)
	defer func() {
		if e := recover(); e != nil {
			t.Logf("PANIC reproduced: %v", e)
			return
		}
		t.Fatalf("no panic: configuration %v", rn.Status().Config)
	}()
	rn.ApplyConfChange(c1) // the application finishes applying C1
}
