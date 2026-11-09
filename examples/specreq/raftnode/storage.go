package raftnode

import (
	"go.etcd.io/raft/v3"
	pb "go.etcd.io/raft/v3/raftpb"
)

// REQ raftnode/bootstrap-from-wal: a detached MemoryStorage rebuilt from a durable image (etcd's
// WAL: snapshot, hard state, entries after it) accepts each write without error.
// Users: server/etcdserver/bootstrap.go:741 (bootstrappedWAL.MemoryStorage),
// examples/raft/kvdurable/storage.go:328-377 (openStorage).
// Assumes: ents are consecutive from snap's index + 1 (the WAL's records after its snapshot),
// below index 2^64; snap is the caller's (a fresh decode), its optional fields present.
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

// REQ raftnode/read-attached: a client reads its node's storage while the node runs: the stored
// snapshot is at least the start's (etcd's run seeds its progress from it), valid, its
// configuration present; the first index is never past the stored snapshot.
// Users: server/etcdserver/server.go:755, 803-812 (run), examples/raft/kvdurable/kv.go:606,
// examples/raft/kvreconf/kv.go:493.
// Assumes: ms is the storage n was started on, holding a snapshot at index si at the start
// (storSnapLb from RestartNode).
// Specs: MemoryStorage.FirstIndex.spec, MemoryStorage.Snapshot.spec; laws: stor_read.spec.
func ReqReadAttached(ms *raft.MemoryStorage, si uint64) uint64 {
	first, _ := ms.FirstIndex()
	snap, err := ms.Snapshot()
	if err != nil || snap.GetMetadata().GetIndex() < si {
		panic("attached storage: a snapshot older than the start's")
	}
	if snap.GetMetadata().GetIndex() != 0 && snap.GetMetadata().GetConfState() == nil {
		panic("attached storage: snapshot without a configuration")
	}
	if first > snap.GetMetadata().GetIndex()+1 {
		panic("attached storage: compacted past its snapshot")
	}
	return first
}

// REQ raftnode/status-progress: a leader's status lists its peers' progress, which the caller
// may range over and index (etcd's isLearnerReady).
// Users: server/etcdserver/server.go:1590-1606.
// Assumes: n is a node of the cluster.
// Specs: node.Status.spec; laws: statusOwn_progress.spec.
func ReqStatusProgress(n raft.Node, id uint64) uint64 {
	st := n.Status()
	var m uint64
	for _, pr := range st.Progress {
		m += pr.Match
	}
	return m + st.Progress[id].Match
}

// REQ raftnode/snapshot-compact: the apply thread snapshots at the applied index (raft's, after
// Advance) and compacts below it and the snapshot; the only errors are ErrSnapOutOfDate (a newer
// snapshot was installed meanwhile) and ErrCompacted.
// Users: server/etcdserver/server.go:2132 (snapshot), 2180 (compact),
// examples/raft/kvdurable/kv.go:585-620.
// Assumes: 0 < applied, at most n's applied index (appliedLb), cs its configuration at applied (the
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
