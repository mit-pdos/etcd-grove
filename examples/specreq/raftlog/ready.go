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
// Assumes: st is the log's attached storage (a MemoryStorage); the previous batch was absorbed;
// no other Step between the Ready and its acknowledgement; the acknowledgement's StableOk holds
// (the entries written are the log's).
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
		last := ents[len(ents)-1]
		l.stableTo(pbEntryID(last))
		if t, err := l.term(last.GetIndex()); err != nil || t != last.GetTerm() {
			panic("ready-cycle: stable entry lost")
		}
	}
	if snap != nil {
		l.stableSnapTo(snap.GetMetadata().GetIndex())
		l.appliedTo(max(l.applied, snap.GetMetadata().GetIndex()), 0)
	}
	if len(committed) > 0 {
		l.appliedTo(committed[len(committed)-1].GetIndex(), entsSize(committed))
	}
}

// REQ raftlog/compact-applied: the client may compact the storage up to an index raft applied
// (and its snapshot), and store a snapshot at one, concurrently with raft's reads; raft's reads
// then answer ErrCompacted only below that index.
// Users: etcd server/etcdserver/server.go (snapshot, then raftStorage.Compact),
// examples/raft/kvdurable (storage compaction).
// Assumes: i was published by raft (raftLog_publish: applied, stable, no snapshot pending), cs and
// data a valid snapshot's at i.
// Specs: MemoryStorage.CreateSnapshot.spec, MemoryStorage.Compact.spec, raftLog.term.spec;
// laws: logStor_createSnapshot.spec, logStor_compact.spec.
func ReqCompactApplied(l *raftLog, st *MemoryStorage, i uint64, cs *pb.ConfState, data []byte) {
	if _, err := st.CreateSnapshot(i, cs, data); err != nil && err != ErrSnapOutOfDate {
		panic("compact-applied: snapshot refused")
	}
	if err := st.Compact(i); err != nil && err != ErrCompacted {
		panic("compact-applied: compaction refused")
	}
	if _, err := l.term(i + 1); err == ErrCompacted {
		panic("compact-applied: compacted past the floor")
	}
}
