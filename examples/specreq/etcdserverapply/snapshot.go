//go:build ignore

// Requirement snippets for etcd's apply thread (batch 2d): snapshots, the raft log's compaction,
// the merged snapshot, a snapshot's install. In package etcdserver (unexported members).
package etcdserver

import (
	"errors"

	"go.etcd.io/raft/v3"
)

// REQ etcdserverapply/snapshot-compact: once raft has advanced past the applied index, the apply
// thread snapshots at it and compacts the raft log below it without a panic (no ErrUnavailable,
// no compaction past raft's applied index: issues/etcd-compact-past-raft-applied.md), and the
// storage then holds a snapshot at or past it.
// Users: server/etcdserver/server.go:1000-1002 (applyAll), 2108-2194.
// Assumes: ep is the apply thread's progress after a batch whose raftAdvancedC was received;
// 0 < ep.appliedi.
// Specs: snapshot.spec, compactRaftLog.spec; R1's MemoryStorage.{CreateSnapshot,Compact,Snapshot}.spec.
func ReqSnapshotCompact(s *EtcdServer, ep *etcdProgress) {
	s.snapshot(ep, false)
	s.compactRaftLog(ep.appliedi)
	sn, err := s.r.raftStorage.Snapshot()
	if err != nil || sn.GetMetadata().GetIndex() < ep.appliedi {
		panic("snapshot-compact: no snapshot at the applied index")
	}
	if _, err := s.r.raftStorage.Term(ep.appliedi); err != nil && !errors.Is(err, raft.ErrCompacted) {
		panic("snapshot-compact: applied index out of the log")
	}
}

// REQ etcdserverapply/merged-snapshot: the matching-term request is sent at the
// index of the database it carries, including while the apply cursor is catching up.
// Users: server/etcdserver/server.go (applyAll), snapshot_merge.go.
// Assumes: ep is the apply thread's progress after processing this Ready.
// Specs: applyAll.spec, createMergedSnapshotMessage.spec, sendMergedSnap.spec.
func ReqMergedSnapshot(s *EtcdServer, ep *etcdProgress, apply *toApply) {
	select {
	case m := <-s.r.msgSnapC:
		if m.GetTerm() == apply.raftTerm {
			want := max(ep.appliedi, s.consistIndex.ConsistentIndex())
			merged := s.createMergedSnapshotMessage(m, ep.appliedt, ep.appliedi, ep.confState, apply.replayTerms, ep.replayConf)
			if merged.GetSnapshot().GetMetadata().GetIndex() != want {
				panic("merged-snapshot: label disagrees with backend progress")
			}
			s.sendMergedSnap(merged)
		}
	default:
	}
}

// REQ etcdserverapply/install-snapshot: a batch's snapshot is installed after the loop saved it:
// the backend opened from its .snap.db is at or past its index (its consistent index), the
// progress moves to its index and term, and no panic (outdated index, open, restore, release).
// Users: server/etcdserver/server.go:1021-1179 (applySnapshot).
// Assumes: ap is a batch with a snapshot handed by raftNode.start; ep is the progress before it.
// Specs: applySnapshot.spec; 2e's OpenSnapshotBackend, Release; 3e's Restore; 3c's Recover.
func ReqInstallSnapshot(s *EtcdServer, ep *etcdProgress, ap *toApply) {
	s.applySnapshot(ep, ap)
	idx := ap.snapshot.GetMetadata().GetIndex()
	if ep.appliedi != idx || ep.appliedt != ap.snapshot.GetMetadata().GetTerm() {
		panic("install-snapshot: progress not at the snapshot")
	}
	if s.consistIndex.ConsistentIndex() < idx {
		panic("install-snapshot: backend behind the snapshot")
	}
}
