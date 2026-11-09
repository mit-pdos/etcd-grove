package raftpb

import (
	"bytes"

	pb "go.etcd.io/raft/v3/raftpb"
	"google.golang.org/protobuf/proto"
)

// REQ raftpb/ensure: EnsureSnapshot of a client-built snapshot (metadata or conf state missing)
// fills what is missing and keeps what the getters read; of an ensured snapshot it changes
// nothing, so it may be called on a snapshot shared read-only (raft's handleSnapshot on a
// received message's snapshot; MemoryStorage.InitialState unlocked).
// Users: storage.go:124/212/222/255 (MemoryStorage), raft.go:1859 (handleSnapshot), raft.go:774,
// 1898 (EnsureConfState of a snapshot's conf state).
// Specs: EnsureSnapshot.spec (both cases), EnsureConfState.spec, Snapshot.GetMetadata.spec,
// SnapshotMetadata.GetConfState.spec, ConfState.GetAutoLeave.spec.
func ReqEnsure(index uint64) {
	s := &pb.Snapshot{Metadata: &pb.SnapshotMetadata{Index: proto.Uint64(index)}}
	s = pb.EnsureSnapshot(s)
	if s.GetMetadata().GetIndex() != index || s.GetMetadata().GetConfState() == nil ||
		s.GetMetadata().GetConfState().GetAutoLeave() {
		panic("ensure")
	}
	if pb.EnsureSnapshot(s) != s || pb.EnsureConfState(s.GetMetadata().GetConfState()) != s.GetMetadata().GetConfState() {
		panic("ensure of an ensured snapshot moved it")
	}
	if pb.EnsureSnapshot(nil).GetMetadata().GetIndex() != 0 {
		panic("ensure of nil")
	}
}

// REQ raftpb/clone-snapshot: a clone of a stored snapshot is a fresh, ensured snapshot with the
// same metadata and data (MemoryStorage.Snapshot/CreateSnapshot hand out clones; unstable keeps one).
// Users: storage.go:213/234/262, log_unstable.go:114/196, log.go:295; etcd raft.go:228.
// Specs: proto's Clone.spec, snapshotPts_msgAt.spec, the getters.
func ReqCloneSnapshot(s *pb.Snapshot) *pb.Snapshot {
	s = pb.EnsureSnapshot(s)
	c := proto.Clone(s).(*pb.Snapshot)
	if c == s || c.GetMetadata().GetTerm() != s.GetMetadata().GetTerm() || !bytes.Equal(c.GetData(), s.GetData()) {
		panic("clone")
	}
	if pb.EnsureSnapshot(c) != c {
		panic("clone not ensured")
	}
	return c
}

// REQ raftpb/bootstrap-bytes: the bootstrap entry of a peer is the same bytes at every founder
// (RawNode.Bootstrap marshals ConfChange{AddNode, id, ctx} at each founder; raft's log matching
// needs equal entries at equal index and term).
// Users: bootstrap.go:52-56 (RawNode.Bootstrap), etcd's bootstrap through StartNode.
// Assumes: ctx is non-empty (etcd's member JSON).
// Specs: bootCC_lit.spec, bootCC_facts.spec, proto's Marshal.spec with 2a's requested determinism
// (marshalOut).
func ReqBootstrapBytes(id uint64, ctx []byte) {
	mk := func() []byte {
		cc := &pb.ConfChange{Type: pb.ConfChangeAddNode.Enum(), NodeId: proto.Uint64(id), Context: ctx}
		data, err := proto.Marshal(cc)
		if err != nil {
			panic("bootstrap marshal")
		}
		return data
	}
	if len(ctx) == 0 {
		return
	}
	if !bytes.Equal(mk(), mk()) {
		panic("founders disagree on the bootstrap entry")
	}
}
