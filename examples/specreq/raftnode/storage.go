package raftnode

import (
	"go.etcd.io/raft/v3"
	pb "go.etcd.io/raft/v3/raftpb"
)

// REQ raftnode/bootstrap-from-wal: a detached MemoryStorage rebuilt from a durable image (etcd's
// WAL: snapshot, hard state, entries after it) accepts each write without error.
// Users: server/etcdserver/bootstrap.go:741 (bootstrappedWAL.MemoryStorage),
// examples/raft/kvdurable/storage.go:328-377 (openStorage).
// Assumes: ents are consecutive from snap's index + 1 (the WAL's records after its snapshot).
// Specs: NewMemoryStorage.spec, MemoryStorage.ApplySnapshot.spec, MemoryStorage.SetHardState.spec,
// MemoryStorage.Append.spec, MemoryStorage.InitialState.spec.
func ReqBootstrapFromWAL(snap *pb.Snapshot, hs *pb.HardState, ents []*pb.Entry) *raft.MemoryStorage {
	s := raft.NewMemoryStorage()
	if snap != nil {
		if err := s.ApplySnapshot(snap); err != nil {
			panic("a fresh storage refused a snapshot")
		}
	}
	if hs != nil {
		_ = s.SetHardState(hs)
	}
	if len(ents) != 0 {
		_ = s.Append(ents) // no gap: the entries follow the snapshot
	}
	gotHS, _, _ := s.InitialState()
	if hs != nil && (gotHS.GetTerm() != hs.GetTerm() || gotHS.GetVote() != hs.GetVote() ||
		gotHS.GetCommit() != hs.GetCommit()) {
		panic("InitialState: not the stored hard state")
	}
	return s
}

// REQ raftnode/snapshot-compact: the apply thread snapshots at the applied index (raft's, after
// Advance) and compacts below it and the snapshot; the only errors are ErrSnapOutOfDate (a newer
// snapshot was installed meanwhile) and ErrCompacted.
// Users: server/etcdserver/server.go:2132 (snapshot), 2180 (compact),
// examples/raft/kvdurable/kv.go:585-620.
// Assumes: applied is at most n's applied index (appliedLb), cs its configuration at applied (the
// last ApplyConfChange's), data the client's state at applied; compact ≤ applied, and
// compact ≤ the stored snapshot's index (a snapshot the caller stored or installed).
// Specs: MemoryStorage.CreateSnapshot.spec, MemoryStorage.Compact.spec; laws: snap_make.spec,
// stor_createSnapshot.spec, stor_compact.spec.
func ReqSnapshotCompact(ms *raft.MemoryStorage, applied uint64, cs *pb.ConfState, data []byte,
	compact uint64) {
	if _, err := ms.CreateSnapshot(applied, cs, data); err != nil && err != raft.ErrSnapOutOfDate {
		panic("CreateSnapshot: " + err.Error())
	}
	if compact == 0 {
		return
	}
	if err := ms.Compact(compact); err != nil && err != raft.ErrCompacted {
		panic("Compact: " + err.Error())
	}
}
