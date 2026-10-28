package durablekv

import (
	"encoding/binary"

	"go.etcd.io/raft/v3"
	pb "go.etcd.io/raft/v3/raftpb"
	"google.golang.org/protobuf/proto"
)

// Storage is a replica's raft storage: a MemoryStorage, which the replica writes whole to its
// durable file (Encode) and reads back on a restart (OpenStorage), and the cluster's voters,
// its configuration (the cluster's never changes).
type Storage struct {
	*raft.MemoryStorage
	voters []uint64
}

// InitialState is the MemoryStorage's hard state (an empty one if it has none: a new
// replica's), with the cluster's voters as the configuration -- also for a new cluster, so that
// a node starts with RestartNode on an empty log rather than by StartNode's bootstrap through
// configuration changes.
func (s *Storage) InitialState() (*pb.HardState, *pb.ConfState, error) {
	hs, _, _ := s.MemoryStorage.InitialState()
	if hs == nil {
		hs = &pb.HardState{}
	}
	return hs, &pb.ConfState{Voters: s.voters}, nil
}

// Snapshot is the MemoryStorage's, but a storage that has never had one (a new cluster's) says
// it has none for now, as the Storage interface asks, rather than returning an empty snapshot.
func (s *Storage) Snapshot() (*pb.Snapshot, error) {
	snap, err := s.MemoryStorage.Snapshot()
	if err == nil && snap.GetMetadata().GetIndex() == 0 {
		return snap, raft.ErrSnapshotTemporarilyUnavailable
	}
	return snap, err
}

// SnapshotIndex is the index of the storage's snapshot (0 if it has none).
func (s *Storage) SnapshotIndex() uint64 {
	snap, _ := s.MemoryStorage.Snapshot()
	return snap.GetMetadata().GetIndex()
}

// putBytes appends b to buf, prefixed by its length (8 bytes, little-endian).
func putBytes(buf []byte, b []byte) []byte {
	var n [8]byte
	binary.LittleEndian.PutUint64(n[:], uint64(len(b)))
	buf = append(buf, n[:]...)
	return append(buf, b...)
}

// getBytes reads back what putBytes wrote at the start of b: the bytes and the rest of b; ok
// is false if b is too short.
func getBytes(b []byte) (v []byte, rest []byte, ok bool) {
	if len(b) < 8 {
		return nil, nil, false
	}
	n := binary.LittleEndian.Uint64(b)
	if uint64(len(b)-8) < n {
		return nil, nil, false
	}
	return b[8 : 8+n], b[8+n:], true
}

// Encode is the storage's contents as its file holds them: its hard state, its snapshot and
// the number of its entries (from its first index on), then each entry, each message as
// proto.Marshal writes it and putBytes prefixes it.
func (s *Storage) Encode() []byte {
	hs, _, _ := s.MemoryStorage.InitialState()
	snap, _ := s.MemoryStorage.Snapshot()
	first, _ := s.MemoryStorage.FirstIndex()
	last, _ := s.MemoryStorage.LastIndex()
	ents, _ := s.MemoryStorage.Entries(first, last+1, ^uint64(0))
	hsb, _ := proto.Marshal(hs)
	snapb, _ := proto.Marshal(snap)
	buf := putBytes(nil, hsb)
	buf = putBytes(buf, snapb)
	var n [8]byte
	binary.LittleEndian.PutUint64(n[:], uint64(len(ents)))
	buf = append(buf, n[:]...)
	for _, e := range ents {
		eb, _ := proto.Marshal(e)
		buf = putBytes(buf, eb)
	}
	return buf
}

// OpenStorage is the storage of a replica of the cluster of voters whose file holds data (ok),
// or a new replica's, empty (no file: !ok). good is false for data Encode did not write.
func OpenStorage(voters []uint64, data string, ok bool) (s *Storage, good bool) {
	s = &Storage{MemoryStorage: raft.NewMemoryStorage(), voters: voters}
	if !ok {
		return s, true
	}
	b := []byte(data)
	hsb, rest, ok1 := getBytes(b)
	if !ok1 {
		return nil, false
	}
	snapb, rest2, ok2 := getBytes(rest)
	if !ok2 || len(rest2) < 8 {
		return nil, false
	}
	hs := &pb.HardState{}
	snap := &pb.Snapshot{}
	if proto.Unmarshal(hsb, hs) != nil || proto.Unmarshal(snapb, snap) != nil {
		return nil, false
	}
	count := binary.LittleEndian.Uint64(rest2)
	rest2 = rest2[8:]
	var ents []*pb.Entry
	for i := uint64(0); i < count; i++ {
		eb, rest3, ok3 := getBytes(rest2)
		if !ok3 {
			return nil, false
		}
		e := &pb.Entry{}
		if proto.Unmarshal(eb, e) != nil {
			return nil, false
		}
		ents = append(ents, e)
		rest2 = rest3
	}
	if len(rest2) != 0 {
		return nil, false
	}
	if snap.GetMetadata().GetIndex() != 0 {
		s.MemoryStorage.ApplySnapshot(snap)
	}
	s.MemoryStorage.SetHardState(hs)
	s.MemoryStorage.Append(ents)
	return s, true
}

// less is the byte-wise order of strings.
func less(a, b string) bool {
	i := 0
	for i < len(a) && i < len(b) {
		if a[i] != b[i] {
			return a[i] < b[i]
		}
		i++
	}
	return len(a) < len(b)
}

// sortStrings sorts ks in increasing order (less), in place: an insertion sort.
func sortStrings(ks []string) {
	for i := 1; i < len(ks); i++ {
		for j := i; j > 0 && less(ks[j], ks[j-1]); j-- {
			ks[j], ks[j-1] = ks[j-1], ks[j]
		}
	}
}

// putMap appends m to buf: the number of its keys (8 bytes, little-endian), then each key and
// its value (each as putBytes writes it), in increasing order of the keys. The order makes it a
// function of the map, whatever order Go iterates it in.
func putMap(buf []byte, m map[string]string) []byte {
	var keys []string
	for k := range m {
		keys = append(keys, k)
	}
	sortStrings(keys)
	var n [8]byte
	binary.LittleEndian.PutUint64(n[:], uint64(len(keys)))
	buf = append(buf, n[:]...)
	for _, k := range keys {
		buf = putBytes(buf, []byte(k))
		buf = putBytes(buf, []byte(m[k]))
	}
	return buf
}

// getMap reads back what putMap wrote at the start of b: the map and the rest of b; ok is false
// for bytes putMap did not write.
func getMap(b []byte) (m map[string]string, rest []byte, ok bool) {
	m = make(map[string]string)
	if len(b) < 8 {
		return nil, nil, false
	}
	n := binary.LittleEndian.Uint64(b)
	b = b[8:]
	for i := uint64(0); i < n; i++ {
		k, rest1, ok1 := getBytes(b)
		if !ok1 {
			return nil, nil, false
		}
		v, rest2, ok2 := getBytes(rest1)
		if !ok2 {
			return nil, nil, false
		}
		m[string(k)] = string(v)
		b = rest2
	}
	return m, b, true
}

// encodeState is a replica's replicated state as a snapshot's data: the store's contents, then
// the operations applied with their answers, each as putMap writes it.
func encodeState(kv map[string]string, applied map[string]string) []byte {
	return putMap(putMap(nil, kv), applied)
}

// decodeState reads back what encodeState wrote, and empty data (the snapshot of a storage that
// has none) as the empty state; ok is false for data it did not write.
func decodeState(b []byte) (kv map[string]string, applied map[string]string, ok bool) {
	if len(b) == 0 {
		return make(map[string]string), make(map[string]string), true
	}
	k, rest, ok1 := getMap(b)
	if !ok1 {
		return nil, nil, false
	}
	a, rest2, ok2 := getMap(rest)
	if !ok2 || len(rest2) != 0 {
		return nil, nil, false
	}
	return k, a, true
}
