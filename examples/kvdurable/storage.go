package kvdurable

import (
	"encoding/binary"

	"go.etcd.io/raft/v3"
	pb "go.etcd.io/raft/v3/raftpb"
	"google.golang.org/protobuf/proto"
)

// Storage is a replica's raft storage: a MemoryStorage, beside the image of the replica's durable
// file (img: the contents the file should hold), which the replica changes together with the
// MemoryStorage (ApplySnapshot, SetHardState, Append, CreateSnapshot, Compact) and writes whole
// to the file (encode), never reading the MemoryStorage back for it, and which openStorage builds
// from the file, with the MemoryStorage, when the replica restarts; that, when raft asks for its
// snapshot (to send to a follower), may answer at random that none is available for now, as the
// Storage interface allows (raft then asks again later); and whose InitialState's configuration
// is the bootstrap one (boot) until it holds a snapshot, and the snapshot's after (every replica,
// a founder or a newcomer, starts at the bootstrap configuration and replays the same
// configurations from the log; one restarted from a snapshot, from the snapshot's).
type Storage struct {
	*raft.MemoryStorage
	boot *pb.ConfState
	// img is the replica's own record of the storage's contents, which encode writes: between two
	// Readys the MemoryStorage's log above the commit index is raft's, its Snapshot does not say
	// which snapshot it returns, and its InitialState reads the hard state without the lock
	// (issues/raft-memorystorage-initialstate-unlocked.md), so the replica reads none of them for
	// its file. Written and read under the replica's dmu, or before the replica's run loop starts
	// (openStorage, newReplica), the only writer once it runs.
	img *image
}

// image is the contents a replica's file holds, kept as the MemoryStorage's calls change them:
// the hard state last set (nil before the first: the zero one), the latest snapshot (never nil;
// an empty one at index 0 before the first), the index and term of the log's start (prev and
// prevTerm: the entry before its first index, the snapshot's or a compaction point), and the
// entries after it, consecutive from prev+1. Nothing is written in place: a change sets new
// snapshots and slices (append copies the entries it keeps).
type image struct {
	hs       *pb.HardState
	snap     *pb.Snapshot
	prev     uint64
	prevTerm uint64
	ents     []*pb.Entry
}

// newStorage is an empty storage of a replica of the cluster bootstrapped at boot: an empty
// MemoryStorage (NewMemoryStorage), and its image: no hard state, the empty snapshot, the log's
// start at index and term 0, no entries.
func newStorage(boot *pb.ConfState) *Storage {
	return &Storage{MemoryStorage: raft.NewMemoryStorage(), boot: boot, img: &image{snap: &pb.Snapshot{}}}
}

// applySnapshot is MemoryStorage.ApplySnapshot of snap (not nil) on the image: ErrSnapOutOfDate,
// and no change, if the image's snapshot is at a non-zero index at least snap's; otherwise the
// snapshot is a copy of snap, and the log starts at it, empty.
func (m *image) applySnapshot(snap *pb.Snapshot) error {
	index := m.snap.GetMetadata().GetIndex()
	if index != 0 && index >= snap.GetMetadata().GetIndex() {
		return raft.ErrSnapOutOfDate
	}
	m.snap = proto.Clone(snap).(*pb.Snapshot)
	m.prev = snap.GetMetadata().GetIndex()
	m.prevTerm = snap.GetMetadata().GetTerm()
	m.ents = nil
	return nil
}

// append is MemoryStorage.Append of entries (consecutive) on the image: no change if there are
// none or all are at or below the log's start; otherwise those above the start (the others are
// dropped) replace the log's entries from the first of them on, the ones after included. It
// panics, as MemoryStorage does, if they start past the log's last index plus one.
func (m *image) append(entries []*pb.Entry) {
	if len(entries) == 0 {
		return
	}
	first := m.prev + 1
	last := entries[0].GetIndex() + uint64(len(entries)) - 1
	if last < first {
		return
	}
	skip := uint64(0)
	if first > entries[0].GetIndex() {
		skip = first - entries[0].GetIndex()
	}
	entries = entries[skip:]
	offset := entries[0].GetIndex() - first
	if offset > uint64(len(m.ents)) {
		panic("kvdurable: a gap in the log")
	}
	m.ents = append(append([]*pb.Entry(nil), m.ents[:offset]...), entries...)
}

// createSnapshot is MemoryStorage.CreateSnapshot of (i, cs, data) on the image:
// ErrSnapOutOfDate, and no change, if i is at most the snapshot's index; otherwise the snapshot
// is at index i, at the term of the log's entry there (the log's start's at its start), of the
// configuration cs (the old snapshot's if cs is nil) and a copy of the data. It panics, as MemoryStorage
// does, if i is outside the log (below its start or past its last index).
func (m *image) createSnapshot(i uint64, cs *pb.ConfState, data []byte) error {
	if i <= m.snap.GetMetadata().GetIndex() {
		return raft.ErrSnapOutOfDate
	}
	if i < m.prev || i > m.prev+uint64(len(m.ents)) {
		panic("kvdurable: a snapshot outside the log")
	}
	term := m.prevTerm
	if i > m.prev {
		term = m.ents[i-m.prev-1].GetTerm()
	}
	if cs == nil {
		cs = m.snap.GetMetadata().GetConfState()
	}
	m.snap = &pb.Snapshot{Metadata: &pb.SnapshotMetadata{ConfState: cs, Index: new(i), Term: new(term)},
		Data: append([]byte(nil), data...)}
	return nil
}

// compact is MemoryStorage.Compact of i on the image: ErrCompacted, and no change, if i is at
// most the log's start; otherwise the log starts at i, with the entries after it. It panics, as
// MemoryStorage does, if i is past the log's last index.
func (m *image) compact(i uint64) error {
	if i <= m.prev {
		return raft.ErrCompacted
	}
	if i > m.prev+uint64(len(m.ents)) {
		panic("kvdurable: a compaction past the log")
	}
	m.prevTerm = m.ents[i-m.prev-1].GetTerm()
	m.ents = m.ents[i-m.prev:]
	m.prev = i
	return nil
}

// ApplySnapshot installs snap (not nil) in the MemoryStorage and the image; the image's answer
// (the MemoryStorage's is the same).
func (s *Storage) ApplySnapshot(snap *pb.Snapshot) error {
	s.MemoryStorage.ApplySnapshot(snap)
	return s.img.applySnapshot(snap)
}

// SetHardState sets the hard state of the MemoryStorage and of the image.
func (s *Storage) SetHardState(hs *pb.HardState) {
	s.img.hs = hs
	s.MemoryStorage.SetHardState(hs)
}

// Append appends entries to the MemoryStorage and the image.
func (s *Storage) Append(entries []*pb.Entry) {
	s.img.append(entries)
	s.MemoryStorage.Append(entries)
}

// CreateSnapshot takes the snapshot (i, cs, data) in the MemoryStorage and the image; the image's
// answer (the MemoryStorage's is the same).
func (s *Storage) CreateSnapshot(i uint64, cs *pb.ConfState, data []byte) error {
	err := s.img.createSnapshot(i, cs, data)
	s.MemoryStorage.CreateSnapshot(i, cs, data)
	return err
}

// Compact compacts the MemoryStorage and the image up to i; the image's answer (the
// MemoryStorage's is the same).
func (s *Storage) Compact(i uint64) error {
	err := s.img.compact(i)
	s.MemoryStorage.Compact(i)
	return err
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

// encode is the storage's contents as its file holds them, read from its image: the hard state
// (term, vote, commit: 8 bytes each), the snapshot (putSnapshot), the index and term of the log's
// start (the entry before its first index: the snapshot's, or a compaction point below it), and
// the entries after it, their number then each (putEntry). The caller holds the replica's dmu, so
// that the contents are those of a moment between two groups of the replica's changes to the
// storage.
func (s *Storage) encode() []byte {
	m := s.img
	buf := putUint64(nil, m.hs.GetTerm())
	buf = putUint64(buf, m.hs.GetVote())
	buf = putUint64(buf, m.hs.GetCommit())
	buf = putSnapshot(buf, m.snap)
	buf = putUint64(buf, m.prev)
	buf = putUint64(buf, m.prevTerm)
	buf = putUint64(buf, uint64(len(m.ents)))
	for _, e := range m.ents {
		buf = putEntry(buf, e)
	}
	return buf
}

// openStorage is the storage of a replica of the cluster bootstrapped at boot whose file holds b,
// as encode wrote it: the same contents, the entries below the snapshot included (MemoryStorage
// has no call that sets them below a snapshot, so it applies a snapshot at the log's start -- the
// stored one if that is where the log starts, an empty one otherwise -- appends the entries, then
// takes the stored snapshot again from them), and its image is the file's contents. good is false
// for bytes encode did not write, or contents raft would not restart from: entries not
// consecutive from the log's start, a snapshot below the log's start or past its end, a commit
// index outside the log.
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
	hs := &pb.HardState{Term: new(term), Vote: new(vote), Commit: new(commit)}
	s.MemoryStorage.SetHardState(hs)
	s.img = &image{hs: hs, snap: snap, prev: prev, prevTerm: prevTerm, ents: ents}
	return s, true
}
