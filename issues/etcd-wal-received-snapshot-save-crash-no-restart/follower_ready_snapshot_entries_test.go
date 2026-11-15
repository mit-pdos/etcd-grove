package raft_test

import (
	"context"
	"io"
	"log"
	"testing"
	"time"

	"go.etcd.io/raft/v3"
	"go.etcd.io/raft/v3/raftpb"
)

// TestFollowerReadySnapshotAndEntries: a follower busy with a Ready (taken
// from Node.Ready, not yet advanced, as etcd's raftNode while it persists) steps the leader's
// MsgSnap(10) and then MsgApp(prev 10, entries 11..12, commit 12). Its next Ready holds the
// snapshot and the entries, which etcd saves as SaveSnap then Save.
func TestFollowerReadySnapshotAndEntries(t *testing.T) {
	ms := raft.NewMemoryStorage()
	ms.Append(cw1Ents(1, 3, 1, 100))
	ms.SetHardState(&raftpb.HardState{Term: cw1U64(1), Vote: cw1U64(1), Commit: cw1U64(3)})
	n := raft.RestartNode(&raft.Config{ID: 2, ElectionTick: 10, HeartbeatTick: 1, Storage: ms,
		MaxSizePerMsg: 1 << 30, MaxInflightMsgs: 256, Logger: &raft.DefaultLogger{Logger: log.New(io.Discard, "", 0)}})
	defer n.Stop()
	ctx := context.Background()
	mt := func(x raftpb.MessageType) *raftpb.MessageType { return &x }
	get := func() raft.Ready {
		select {
		case rd := <-n.Ready():
			return rd
		case <-time.After(5 * time.Second):
			t.Fatal("no Ready")
		}
		return raft.Ready{}
	}
	n.Step(ctx, &raftpb.Message{Type: mt(raftpb.MessageType_MsgHeartbeat), From: cw1U64(1), To: cw1U64(2), Term: cw1U64(2), Commit: cw1U64(3)})
	rd1 := get()
	n.Step(ctx, &raftpb.Message{Type: mt(raftpb.MessageType_MsgSnap), From: cw1U64(1), To: cw1U64(2), Term: cw1U64(2),
		Snapshot: &raftpb.Snapshot{Metadata: &raftpb.SnapshotMetadata{Index: cw1U64(10), Term: cw1U64(2), ConfState: &raftpb.ConfState{Voters: []uint64{1, 2, 3}}}}})
	n.Step(ctx, &raftpb.Message{Type: mt(raftpb.MessageType_MsgApp), From: cw1U64(1), To: cw1U64(2), Term: cw1U64(2),
		LogTerm: cw1U64(2), Index: cw1U64(10), Entries: cw1Ents(11, 12, 2, 100), Commit: cw1U64(12)})
	ms.SetHardState(rd1.HardState)
	n.Advance()
	rd2 := get()
	t.Logf("Ready: snapshot %d, hard state %v, %d entries", rd2.Snapshot.GetMetadata().GetIndex(), rd2.HardState, len(rd2.Entries))
	if raft.IsEmptySnap(rd2.Snapshot) || len(rd2.Entries) == 0 {
		t.Fatal("no Ready with both")
	}
}

func cw1U64(x uint64) *uint64 { return &x }

func cw1Ents(lo, hi, term uint64, size int) []*raftpb.Entry {
	var es []*raftpb.Entry
	for i := lo; i <= hi; i++ {
		es = append(es, &raftpb.Entry{Index: cw1U64(i), Term: cw1U64(term), Type: raftpb.EntryType_EntryNormal.Enum(), Data: make([]byte, size)})
	}
	return es
}
