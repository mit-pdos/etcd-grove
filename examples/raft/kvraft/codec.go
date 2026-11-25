package kvraft

import (
	"encoding/binary"

	"github.com/goose-lang/primitive"
	"go.etcd.io/raft/v3/confchange"
	pb "go.etcd.io/raft/v3/raftpb"
	"go.etcd.io/raft/v3/tracker"
)

// This file is kvdurable's encodings and checks (examples/raft/kvdurable/kv.go), unchanged: the
// operations as log entries, the reads' contexts, the replicated state as a snapshot's data, and
// the store's decision on a committed configuration change.

const (
	opPut  = 1
	opGet  = 2
	opRead = 3
)

// oneIn is true with probability 1/n.
func oneIn(n uint64) bool {
	return primitive.RandomUint64()%n == 0
}

// below is a random number in [0, n) (0 if n is 0).
func below(n uint64) uint64 {
	if n == 0 {
		return 0
	}
	return primitive.RandomUint64() % n
}

// encode is an operation as a log entry: its id (8 bytes, little-endian), the kind (1 byte),
// the key's length (8 bytes), the key, then the value (the rest; empty for a Get). A read's
// context (Read) is encoded the same way, after the replica's id (8 bytes), with the read's
// sequence number as the id, of kind opRead.
func encode(id uint64, kind byte, key, val string) []byte {
	b := make([]byte, 17, 17+len(key)+len(val))
	binary.LittleEndian.PutUint64(b, id)
	b[8] = kind
	binary.LittleEndian.PutUint64(b[9:], uint64(len(key)))
	b = append(b, []byte(key)...)
	return append(b, []byte(val)...)
}

// decode reads back what encode wrote; ok is false for an entry that is not an operation
// (raft's empty entries, which a new leader appends and which replace a refused
// configuration change).
func decode(b []byte) (id uint64, kind byte, key, val string, ok bool) {
	if len(b) < 17 {
		return 0, 0, "", "", false
	}
	n := binary.LittleEndian.Uint64(b[9:])
	if uint64(len(b)-17) < n {
		return 0, 0, "", "", false
	}
	return binary.LittleEndian.Uint64(b), b[8], string(b[17 : 17+n]), string(b[17+n:]), true
}

// readCtx is the context of a read: the replica, its read's sequence number there, and the key.
func readCtx(replica, seq uint64, key string) []byte {
	b := make([]byte, 8)
	binary.LittleEndian.PutUint64(b, replica)
	return append(b, encode(seq, opRead, key, "")...)
}

// decodeReadCtx reads back what readCtx wrote.
func decodeReadCtx(b []byte) (replica, seq uint64, key string, ok bool) {
	if len(b) < 8 {
		return 0, 0, "", false
	}
	seq, kind, key, _, ok := decode(b[8:])
	if !ok || kind != opRead {
		return 0, 0, "", false
	}
	return binary.LittleEndian.Uint64(b), seq, key, true
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
// its value (each as putBytes writes it), in increasing order of the keys, so that it is a
// function of the map.
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

// encodeState is a replica's replicated state as a snapshot's data: the store's contents and
// the operations applied with their answers, each as putMap writes it. The configuration is
// the snapshot's metadata's.
func encodeState(kv map[string]string, applied map[string]string) []byte {
	return putMap(putMap(nil, kv), applied)
}

// decodeState reads back what encodeState wrote; ok is false for data it did not write.
func decodeState(b []byte) (kv map[string]string, applied map[string]string, ok bool) {
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

// validConf says whether applying cc to a node whose configuration is cs succeeds: raft's own
// check (raft.applyConfChange runs the same confchange functions on its tracker, and panics on
// their error), run on the configuration restored from cs (as raft restores a snapshot's).
func validConf(cs *pb.ConfState, cc *pb.ConfChangeV2) bool {
	if cs == nil {
		cs = &pb.ConfState{}
	}
	cfg, prs, err := confchange.Restore(confchange.Changer{Tracker: tracker.MakeProgressTracker(1, 0), LastIndex: 1}, cs)
	if err != nil {
		return false
	}
	trk := tracker.MakeProgressTracker(1, 0)
	trk.Config = cfg
	trk.Progress = prs
	chg := confchange.Changer{Tracker: trk, LastIndex: 1}
	var after tracker.ProgressMap
	if cc.LeaveJoint() {
		_, after, err = chg.LeaveJoint()
	} else if autoLeave, ok := cc.EnterJoint(); ok {
		_, after, err = chg.EnterJoint(autoLeave, cc.GetChanges()...)
	} else {
		_, after, err = chg.Simple(cc.GetChanges()...)
	}
	// the configurations the protocol admits have fewer than 2^62 members, and a snapshot's conf
	// state lists at most 2^62 ids in all (a joint configuration's voters may be listed twice, as
	// incoming and outgoing): checked as fewer than 2^61 members (never reached here, with at most
	// maxReplicas of them, but checked so that a change it accepts is one raft's protocol allows and
	// a snapshot at its configuration one raft's storage takes: the store's decision on a committed
	// conf entry, the same at every replica)
	return err == nil && uint64(len(after)) < 1<<61
}

// maxIndex bounds the indices of the entries a Storage holds (the bound raft's Storage contract
// assumes of the stable log, 2^61): a replica stops before its log outgrows it (run).
const maxIndex = 1 << 61

// fits says whether appending es keeps the stored log within maxIndex.
func fits(es []*pb.Entry) bool {
	return len(es) == 0 || (uint64(len(es)) <= maxIndex && es[0].GetIndex() <= maxIndex-uint64(len(es)))
}
