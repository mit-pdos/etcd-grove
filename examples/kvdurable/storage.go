package kvdurable

import (
	"encoding/binary"

	"go.etcd.io/raft/v3"
	pb "go.etcd.io/raft/v3/raftpb"
	"google.golang.org/protobuf/proto"
)

// Storage is a replica's raft storage: a MemoryStorage, which the replica writes whole to its
// durable file (encode) and reads back when it restarts (openStorage); that, when raft asks for
// its snapshot (to send to a follower), may answer at random that none is available for now, as
// the Storage interface allows (raft then asks again later); and whose InitialState's
// configuration is the bootstrap one (boot) until it holds a snapshot, and the snapshot's after
// (every replica, a founder or a newcomer, starts at the bootstrap configuration and replays the
// same configurations from the log; one restarted from a snapshot, from the snapshot's).
type Storage struct {
	*raft.MemoryStorage
	boot *pb.ConfState
	// hs is the hard state last set (SetHardState), the replica's own copy: MemoryStorage's
	// InitialState reads its fields without the lock (issues/raft-memorystorage-initialstate-unlocked.md),
	// so once a node runs on the storage it is called by raft only (at the node's start), never by
	// the replica. Written and read under the replica's dmu, or before the replica's run loop
	// starts (openStorage, newReplica), the only writer once it runs.
	hs *pb.HardState
}

// SetHardState sets the storage's hard state, and the replica's copy (hs).
func (s *Storage) SetHardState(hs *pb.HardState) {
	s.MemoryStorage.SetHardState(hs)
	s.hs = hs
}

// snapIndex is the index of the storage's snapshot (0 if it has none).
func (s *Storage) snapIndex() uint64 {
	snap, _ := s.MemoryStorage.Snapshot()
	return snap.GetMetadata().GetIndex()
}

// InitialState is the MemoryStorage's hard state, with the snapshot's configuration, or the
// bootstrap one if the storage has no snapshot.
func (s *Storage) InitialState() (*pb.HardState, *pb.ConfState, error) {
	hs, cs, err := s.MemoryStorage.InitialState()
	if s.snapIndex() == 0 {
		cs = s.boot
	}
	return hs, proto.Clone(cs).(*pb.ConfState), err
}

// Snapshot is the MemoryStorage's, or, one time in four, ErrSnapshotTemporarilyUnavailable.
func (s *Storage) Snapshot() (*pb.Snapshot, error) {
	if oneIn(4) {
		return nil, raft.ErrSnapshotTemporarilyUnavailable
	}
	return s.MemoryStorage.Snapshot()
}

// putUint64 appends x to buf (8 bytes, little-endian).
func putUint64(buf []byte, x uint64) []byte {
	var n [8]byte
	binary.LittleEndian.PutUint64(n[:], x)
	return append(buf, n[:]...)
}

// getUint64 reads back what putUint64 wrote at the start of b, and the rest of b; ok is false if
// b is too short.
func getUint64(b []byte) (x uint64, rest []byte, ok bool) {
	if len(b) < 8 {
		return 0, nil, false
	}
	return binary.LittleEndian.Uint64(b), b[8:], true
}

// putIDs appends ids to buf: their number, then each (putUint64).
func putIDs(buf []byte, ids []uint64) []byte {
	buf = putUint64(buf, uint64(len(ids)))
	for _, id := range ids {
		buf = putUint64(buf, id)
	}
	return buf
}

// getIDs reads back what putIDs wrote at the start of b.
func getIDs(b []byte) (ids []uint64, rest []byte, ok bool) {
	n, rest, ok := getUint64(b)
	if !ok || uint64(len(rest))/8 < n {
		return nil, nil, false
	}
	for i := uint64(0); i < n; i++ {
		id, rest2, _ := getUint64(rest)
		ids = append(ids, id)
		rest = rest2
	}
	return ids, rest, true
}

// putEntry appends e to buf: its term, index and type (8 bytes each), then its data (putBytes).
func putEntry(buf []byte, e *pb.Entry) []byte {
	buf = putUint64(buf, e.GetTerm())
	buf = putUint64(buf, e.GetIndex())
	buf = putUint64(buf, uint64(e.GetType()))
	return putBytes(buf, e.GetData())
}

// getEntry reads back what putEntry wrote at the start of b.
func getEntry(b []byte) (e *pb.Entry, rest []byte, ok bool) {
	term, r1, ok1 := getUint64(b)
	index, r2, ok2 := getUint64(r1)
	typ, r3, ok3 := getUint64(r2)
	if !ok1 || !ok2 || !ok3 || typ > 2 {
		return nil, nil, false
	}
	data, r4, ok4 := getBytes(r3)
	if !ok4 {
		return nil, nil, false
	}
	return &pb.Entry{Term: new(term), Index: new(index), Type: pb.EntryType(typ).Enum(), Data: data}, r4, true
}

// putSnapshot appends snap to buf: its index and term, its configuration (the voters, learners,
// outgoing voters and next learners, each as putIDs writes them, then auto-leave, 1 byte), then
// its data (putBytes).
func putSnapshot(buf []byte, snap *pb.Snapshot) []byte {
	md := snap.GetMetadata()
	cs := md.GetConfState()
	buf = putUint64(buf, md.GetIndex())
	buf = putUint64(buf, md.GetTerm())
	buf = putIDs(buf, cs.GetVoters())
	buf = putIDs(buf, cs.GetLearners())
	buf = putIDs(buf, cs.GetVotersOutgoing())
	buf = putIDs(buf, cs.GetLearnersNext())
	if cs.GetAutoLeave() {
		buf = append(buf, 1)
	} else {
		buf = append(buf, 0)
	}
	return putBytes(buf, snap.GetData())
}

// getSnapshot reads back what putSnapshot wrote at the start of b.
func getSnapshot(b []byte) (snap *pb.Snapshot, rest []byte, ok bool) {
	index, r1, ok1 := getUint64(b)
	term, r2, ok2 := getUint64(r1)
	voters, r3, ok3 := getIDs(r2)
	learners, r4, ok4 := getIDs(r3)
	outgoing, r5, ok5 := getIDs(r4)
	next, r6, ok6 := getIDs(r5)
	if !ok1 || !ok2 || !ok3 || !ok4 || !ok5 || !ok6 || len(r6) < 1 {
		return nil, nil, false
	}
	autoLeave := r6[0] == 1
	data, r7, ok7 := getBytes(r6[1:])
	if !ok7 {
		return nil, nil, false
	}
	cs := &pb.ConfState{Voters: voters, Learners: learners, VotersOutgoing: outgoing,
		LearnersNext: next, AutoLeave: new(autoLeave)}
	return &pb.Snapshot{Metadata: &pb.SnapshotMetadata{ConfState: cs, Index: new(index), Term: new(term)},
		Data: data}, r7, true
}

// encode is the storage's contents as its file holds them: its hard state (term, vote, commit:
// 8 bytes each), its snapshot (putSnapshot), the index and term of the log's start (the entry
// before its first index: the snapshot's, or a compaction point below it), and the entries after
// it, their number then each (putEntry). The caller holds the replica's dmu, so that the contents
// are those of a moment between two groups of the replica's writes to the storage.
func (s *Storage) encode() []byte {
	hs := s.hs
	snap, _ := s.MemoryStorage.Snapshot()
	first, _ := s.MemoryStorage.FirstIndex()
	last, _ := s.MemoryStorage.LastIndex()
	prevTerm, _ := s.MemoryStorage.Term(first - 1)
	var ents []*pb.Entry
	if last >= first {
		ents, _ = s.MemoryStorage.Entries(first, last+1, ^uint64(0))
	}
	buf := putUint64(nil, hs.GetTerm())
	buf = putUint64(buf, hs.GetVote())
	buf = putUint64(buf, hs.GetCommit())
	buf = putSnapshot(buf, snap)
	buf = putUint64(buf, first-1)
	buf = putUint64(buf, prevTerm)
	buf = putUint64(buf, uint64(len(ents)))
	for _, e := range ents {
		buf = putEntry(buf, e)
	}
	return buf
}

// openStorage is the storage of a replica of the cluster bootstrapped at boot whose file holds b,
// as encode wrote it: the same contents, the entries below the snapshot included (MemoryStorage
// has no call that sets them below a snapshot, so it applies a snapshot at the log's start -- the
// stored one if that is where the log starts, an empty one otherwise -- appends the entries, then
// takes the stored snapshot again from them). good is false for bytes encode did not write, or
// contents raft would not restart from: entries not consecutive from the log's start, a snapshot
// below the log's start or past its end, a commit index outside the log.
func openStorage(boot *pb.ConfState, b []byte) (s *Storage, good bool) {
	s = &Storage{MemoryStorage: raft.NewMemoryStorage(), boot: boot}
	term, r1, ok1 := getUint64(b)
	vote, r2, ok2 := getUint64(r1)
	commit, r3, ok3 := getUint64(r2)
	if !ok1 || !ok2 || !ok3 {
		return nil, false
	}
	snap, r4, ok4 := getSnapshot(r3)
	prev, r5, ok5 := getUint64(r4)
	prevTerm, r6, ok6 := getUint64(r5)
	n, rest, ok7 := getUint64(r6)
	if !ok4 || !ok5 || !ok6 || !ok7 || prev >= maxIndex || n > maxIndex-prev {
		return nil, false
	}
	var ents []*pb.Entry
	for i := uint64(0); i < n; i++ {
		e, rest2, ok := getEntry(rest)
		if !ok || e.GetIndex() != prev+1+i {
			return nil, false
		}
		ents = append(ents, e)
		rest = rest2
	}
	si := snap.GetMetadata().GetIndex()
	last := prev + n
	if len(rest) != 0 || si < prev || si > last || commit < prev || commit > last {
		return nil, false
	}
	if prev > 0 {
		base := snap
		if si != prev {
			base = &pb.Snapshot{Metadata: &pb.SnapshotMetadata{Index: new(prev), Term: new(prevTerm)}}
		}
		s.MemoryStorage.ApplySnapshot(base)
	}
	s.MemoryStorage.Append(ents)
	if si > prev {
		s.MemoryStorage.CreateSnapshot(si, snap.GetMetadata().GetConfState(), snap.GetData())
	}
	s.SetHardState(&pb.HardState{Term: new(term), Vote: new(vote), Commit: new(commit)})
	return s, true
}
