//go:build ignore

// Requirement snippets for raft's log (batch R3): the Ready cycle as rawnode.go drives the log
// (synchronous storage writes), and the client's writes to the attached storage.
package raft

import (
	pb "go.etcd.io/raft/v3/raftpb"
)

// REQ raftlog/ready-cycle: a Ready hands out the unstable entries (and snapshot) not yet in
// progress and the committed entries to apply; the client installs the snapshot, appends the
// entries (no gap), applies; the acknowledgement makes them stable and applied, after which the
// log reads them from the storage unchanged and hands nothing out twice.
// Users: rawnode.go:140-160,425-440 (readyWithoutAccept, acceptReady), raft.go:1215-1228
// (MsgStorageAppendResp, MsgStorageApplyResp), etcd's raftNode loop (server/etcdserver/raft.go).
// Assumes: st is the log's attached storage (a MemoryStorage); the previous batch was absorbed
// (raftLog_absorb, at the previous acknowledgement) and this one is absorbed after the writes,
// before stableTo; no other Step between the Ready and its acknowledgement, so StableOk follows
// from Wf's in-progress agreement; the committed range fits in memory (< 2^63 entries).
// Specs: raftLog.nextUnstableEnts.spec, raftLog.nextUnstableSnapshot.spec,
// raftLog.nextCommittedEnts.spec, raftLog.acceptUnstable.spec, raftLog.acceptApplying.spec,
// raftLog.stableTo.spec, raftLog.stableSnapTo.spec, raftLog.appliedTo.spec, entsSize.spec;
// laws: logStor_install.spec, logStor_append.spec, logPending_noEnts.spec, raftLog_absorb.spec,
// raftLog_publish.spec, MemoryStorage.Append.spec, MemoryStorage.ApplySnapshot.spec.
func ReqReadyCycle(l *raftLog, st *MemoryStorage) {
	ents := l.nextUnstableEnts()
	snap := l.nextUnstableSnapshot()
	committed := l.nextCommittedEnts(true)
	l.acceptUnstable()
	if len(committed) > 0 {
		l.acceptApplying(committed[len(committed)-1].GetIndex(), entsSize(committed), true)
	}
	if snap != nil {
		if err := st.ApplySnapshot(snap); err != nil {
			panic("ready-cycle: storage refused the snapshot")
		}
	}
	if err := st.Append(ents); err != nil {
		panic("ready-cycle: append failed")
	}
	if len(l.nextUnstableEnts()) != 0 || l.hasNextUnstableSnapshot() {
		panic("ready-cycle: handed out twice")
	}
	if len(ents) > 0 {
		l.stableTo(pbEntryID(ents[len(ents)-1]))
	}
	if snap != nil {
		l.stableSnapTo(snap.GetMetadata().GetIndex())
		l.appliedTo(max(l.applied, snap.GetMetadata().GetIndex()), 0)
	}
	if len(ents) > 0 {
		// after stableSnapTo: with a snapshot still pending, lastIndex is the snapshot's
		last := ents[len(ents)-1]
		if t, err := l.term(last.GetIndex()); err != nil || t != last.GetTerm() {
			panic("ready-cycle: stable entry lost")
		}
	}
	if len(committed) > 0 {
		l.appliedTo(committed[len(committed)-1].GetIndex(), entsSize(committed))
	}
}

// REQ raftlog/compact-applied: the client may compact the storage up to an index raft applied
// (and its snapshot), and store a snapshot at one, concurrently with raft's reads; raft's reads
// at the applied index then still answer.
// Users: etcd server/etcdserver/server.go (snapshot, then raftStorage.Compact),
// examples/raft/kvdurable (storage compaction).
// Assumes: i is the log's applied index, published by raft (raftLog_publish), and no other
// compaction runs; cs and data a valid snapshot's at i; no snapshot pending.
// Specs: MemoryStorage.CreateSnapshot.spec, MemoryStorage.Compact.spec, raftLog.term.spec;
// laws: logStor_createSnapshot.spec, logStor_compact.spec.
func ReqCompactApplied(l *raftLog, st *MemoryStorage, i uint64, cs *pb.ConfState, data []byte) {
	if _, err := st.CreateSnapshot(i, cs, data); err != nil && err != ErrSnapOutOfDate {
		panic("compact-applied: snapshot refused")
	}
	if err := st.Compact(i); err != nil && err != ErrCompacted {
		panic("compact-applied: compaction refused")
	}
	if _, err := l.term(i); err == ErrCompacted {
		panic("compact-applied: compacted past the floor")
	}
}

// REQ raftlog/move-before-advance: between a Ready and its Advance the log may move (a
// truncating MsgApp from a new leader, or a newer snapshot restored); the acknowledgement is then
// ignored where it no longer matches, and the applied index is still published, so the client
// may compact its storage up to it.
// Users: node.go:354-394 (run steps recvc while advancec is armed), raft.go:1215-1228,
// etcd server/etcdserver/server.go (compaction after Advance).
// Assumes: as ReqReadyCycle, but a step (truncate, or restore of s2 past committed) between the
// hand-out and the acknowledgement; committed covers the applied entries handed out.
// Specs: raftLog.append.spec, raftLog.restore.spec, raftLog.stableTo.spec, raftLog.appliedTo.spec;
// laws: raftLog_absorb.spec, raftLog_publish.spec (from frozen), logStor_compact.spec.
func ReqMoveBeforeAdvance(l *raftLog, st *MemoryStorage, newer []*pb.Entry, s2 *pb.Snapshot) {
	ents := l.nextUnstableEnts()
	committed := l.nextCommittedEnts(true)
	l.acceptUnstable()
	if s2 != nil {
		l.restore(s2)
	} else if len(newer) > 0 {
		l.append(newer...) // above committed
	}
	if err := st.Append(ents); err != nil {
		panic("move-before-advance: append failed")
	}
	if len(ents) > 0 {
		l.stableTo(pbEntryID(ents[len(ents)-1])) // may be ignored
	}
	if len(committed) > 0 {
		i := committed[len(committed)-1].GetIndex()
		l.appliedTo(i, entsSize(committed))
		if err := st.Compact(i); err != nil && err != ErrCompacted {
			panic("move-before-advance: compaction refused")
		}
	}
}
