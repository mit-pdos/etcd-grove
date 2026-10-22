// Package kv is a minimal replicated application on raft: a string-to-string key-value
// store with Put, Get and Append, replicated by a raft Node on each of a cluster's replicas.
// It is an example for verification: every operation, Get included, goes through the raft
// log, so each one takes effect at the point its entry is committed. Read is a
// linearizable read of a key that does not go through the log: it asks raft for a read
// index (Node.ReadIndex, raft's ReadOnlySafe read-only queries) and answers once the
// replica has applied the log up to it.
package kv

import (
	"context"
	"encoding/binary"
	"sync"

	"go.etcd.io/raft/v3"
	pb "go.etcd.io/raft/v3/raftpb"
	"google.golang.org/protobuf/proto"
)

const (
	opPut    = 1
	opGet    = 2
	opRead   = 3
	opAppend = 4
)

// encode is an operation as a log entry: the proposing replica (8 bytes, little-endian),
// its sequence number there (8 bytes), the kind (1 byte), the key's length (8 bytes), the
// key, then the value (the rest; empty for a Get). A read's context (Read) is encoded the
// same way, of kind opRead, with the key it reads.
func encode(replica, seq uint64, kind byte, key, val string) []byte {
	b := make([]byte, 25, 25+len(key)+len(val))
	binary.LittleEndian.PutUint64(b, replica)
	binary.LittleEndian.PutUint64(b[8:], seq)
	b[16] = kind
	binary.LittleEndian.PutUint64(b[17:], uint64(len(key)))
	b = append(b, []byte(key)...)
	return append(b, []byte(val)...)
}

// decode reads back what encode wrote; ok is false for an entry that is not an
// operation (raft's empty entries, which a new leader appends).
func decode(b []byte) (replica, seq uint64, kind byte, key, val string, ok bool) {
	if len(b) < 25 {
		return 0, 0, 0, "", "", false
	}
	n := binary.LittleEndian.Uint64(b[17:])
	if uint64(len(b)-25) < n {
		return 0, 0, 0, "", "", false
	}
	return binary.LittleEndian.Uint64(b), binary.LittleEndian.Uint64(b[8:]), b[16],
		string(b[25 : 25+n]), string(b[25+n:]), true
}

// Storage is a replica's raft storage for a new cluster: a MemoryStorage whose initial
// configuration is the cluster's voters (a fresh MemoryStorage has none, and raft starts
// from a storage's InitialState), so that a node starts with RestartNode on an empty log
// rather than by StartNode's bootstrap through configuration changes.
type Storage struct {
	*raft.MemoryStorage
	voters []uint64
}

// NewStorage is an empty storage for a member of the cluster of voters.
func NewStorage(voters []uint64) *Storage {
	return &Storage{MemoryStorage: raft.NewMemoryStorage(), voters: voters}
}

// InitialState is a new cluster's: no hard state (the store persists only the log's
// entries, never a HardState, so the MemoryStorage's is always empty), and the cluster's
// voters as the configuration.
func (s *Storage) InitialState() (*pb.HardState, *pb.ConfState, error) {
	return &pb.HardState{}, &pb.ConfState{Voters: s.voters}, nil
}

// Snapshot is the MemoryStorage's, but a storage that has never had one (a new
// cluster's) says it has none for now, as the Storage interface asks, rather than
// returning an empty snapshot.
func (s *Storage) Snapshot() (*pb.Snapshot, error) {
	snap, err := s.MemoryStorage.Snapshot()
	if err == nil && snap.GetMetadata().GetIndex() == 0 {
		return snap, raft.ErrSnapshotTemporarilyUnavailable
	}
	return snap, err
}

// KV is one replica: its id, the raft node, its storage, the store's contents as of the
// last applied entry, the operations applied (by their encoding, each with its key's value right
// after it: what the operation answers), the operations of this replica waiting for theirs and
// its reads waiting for their answer (both by sequence number).
type KV struct {
	id      uint64
	node    raft.Node
	storage *Storage

	mu      sync.Mutex
	kv      map[string]string
	nextSeq uint64
	applied map[string]string
	waiters map[uint64]chan string
	reads   map[uint64]chan string
}

// New starts replica id on a running node and its storage; send delivers the node's
// messages to the other replicas.
func New(id uint64, node raft.Node, storage *Storage, send func([]*pb.Message)) *KV {
	r := &KV{id: id, node: node, storage: storage, kv: make(map[string]string),
		applied: make(map[string]string), waiters: make(map[uint64]chan string),
		reads: make(map[uint64]chan string)}
	go r.run(send)
	return r
}

// maxIndex bounds the indices of the entries a Storage holds (the bound raft's Storage
// contract assumes of the stable log, 2^61).
const maxIndex = 1 << 61

// snapEvery is the number of entries a replica applies between two of its snapshots, and
// snapMargin the number of entries below a new snapshot's index its storage keeps: the log is
// compacted to the snapshot's index minus snapMargin, so that a follower a little behind is
// still sent entries rather than the snapshot.
const (
	snapEvery  = 100
	snapMargin = 10
)

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

// fits says whether appending es keeps the stored log within maxIndex.
func fits(es []*pb.Entry) bool {
	return len(es) == 0 || (uint64(len(es)) <= maxIndex && es[0].GetIndex() <= maxIndex-uint64(len(es)))
}

// run handles the node's Readys: install the snapshot, if any, persist the entries, send the
// messages, note the read states, apply the committed entries in order (a configuration
// change, RemoveMember's, to the node: Node.ApplyConfChange, before the Advance that
// acknowledges it, as raft needs), answer the reads whose index is applied, then Advance. A
// log that would outgrow maxIndex stops the replica (2^61 entries: it does not happen). The
// applied index is the number of entries applied: the log starts empty, at index 1.
//
// Snapshots: a Ready's snapshot (one of another replica's, which this one lags too far behind
// to be sent entries) is installed before the entries after it are appended: its data, the
// replicated state of the log up to its index (encodeState), replaces the store's contents and
// the operations applied (install, which answers this replica's operations among them), the
// applied index jumps to its index, and the storage applies it.
// Data that does not decode stops the replica (every snapshot is a replica's, encodeState's: it
// does not happen). After the Advance, every snapEvery applied entries, the replica takes a
// snapshot of its state at the applied index, with the cluster's voters as its configuration,
// and compacts its log up to snapMargin entries below it -- unless it has applied a
// configuration change, after which the voters are no longer the configuration and it takes
// no more snapshots (a snapshot it installs is of an index before any configuration change,
// as every snapshot is).
func (r *KV) run(send func([]*pb.Message)) {
	var pending []raft.ReadState
	var applied uint64
	var snapIndex uint64
	reconf := false
	for rd := range r.node.Ready() {
		if !fits(rd.Entries) {
			for {
			}
		}
		if rd.Snapshot != nil {
			kv, ops, ok := decodeState(rd.Snapshot.GetData())
			if !ok {
				for {
				}
			}
			r.install(kv, ops)
			applied = rd.Snapshot.GetMetadata().GetIndex()
			snapIndex = applied
			r.storage.ApplySnapshot(rd.Snapshot)
		}
		r.storage.Append(rd.Entries)
		send(rd.Messages)
		pending = append(pending, rd.ReadStates...)
		for _, e := range rd.CommittedEntries {
			if e.GetType() == pb.EntryConfChange {
				var cc pb.ConfChange
				proto.Unmarshal(e.GetData(), &cc)
				r.node.ApplyConfChange(&cc)
				reconf = true
			}
			r.apply(e)
			applied++
		}
		pending = r.answer(pending, applied)
		r.node.Advance()
		if !reconf && applied-snapIndex >= snapEvery {
			r.mu.Lock()
			data := encodeState(r.kv, r.applied)
			r.mu.Unlock()
			r.storage.CreateSnapshot(applied, &pb.ConfState{Voters: r.storage.voters}, data)
			snapIndex = applied
			if applied > snapMargin {
				r.storage.Compact(applied - snapMargin)
			}
		}
	}
}

// install replaces the store's contents and the operations applied by a snapshot's (decoded,
// decodeState), and answers each operation of this replica's waiting for its answer whose
// encoding is among the snapshot's operations applied -- one the snapshot covers, whose entry
// this replica does not apply -- with the key's value after it the snapshot records: what apply
// would have sent.
func (r *KV) install(kv map[string]string, applied map[string]string) {
	r.mu.Lock()
	r.kv = kv
	r.applied = applied
	for o, v := range applied {
		replica, seq, _, _, _, ok := decode([]byte(o))
		if ok && replica == r.id {
			ch, found := r.waiters[seq]
			if found {
				delete(r.waiters, seq)
				ch <- v
			}
		}
	}
	r.mu.Unlock()
}

// answer answers the pending reads whose index is at most applied with the current value
// of the key they read (that of the log up to applied), and returns the others. A read
// state that is not one of this replica's reads waiting for its answer is dropped (raft
// hands out a node's read states only to that node, so a read's context is always its own
// replica's).
func (r *KV) answer(pending []raft.ReadState, applied uint64) []raft.ReadState {
	var rest []raft.ReadState
	for _, rs := range pending {
		if applied < rs.Index {
			rest = append(rest, rs)
			continue
		}
		replica, seq, kind, key, _, ok := decode(rs.RequestCtx)
		if !ok || replica != r.id || kind != opRead {
			continue
		}
		r.mu.Lock()
		ch, found := r.reads[seq]
		if found {
			delete(r.reads, seq)
		}
		v := r.kv[key]
		r.mu.Unlock()
		if found {
			ch <- v
		}
	}
	return rest
}

// apply runs one committed entry: a Put sets its key's value, an Append appends to it;
// any kind answers its waiter, if this replica proposed it, with the key's value after the
// operation, which the table of the operations applied records. An entry whose operation was
// already applied (an operation may be committed
// more than once: a proposal retried after an error, or delivered twice) is skipped, so
// that an operation takes effect once. Operations are told apart by their encoding, which
// is unique: the replica and a sequence number of its own.
func (r *KV) apply(e *pb.Entry) {
	if e.GetType() != pb.EntryNormal {
		return
	}
	replica, seq, kind, key, val, ok := decode(e.GetData())
	if !ok {
		return
	}
	r.mu.Lock()
	if _, done := r.applied[string(e.GetData())]; done {
		r.mu.Unlock()
		return
	}
	if kind == opPut {
		r.kv[key] = val
	} else if kind == opAppend {
		r.kv[key] = r.kv[key] + val
	}
	v := r.kv[key]
	r.applied[string(e.GetData())] = v
	var ch chan string
	found := false
	if replica == r.id {
		ch, found = r.waiters[seq]
		if found {
			delete(r.waiters, seq)
		}
	}
	r.mu.Unlock()
	if found {
		ch <- v
	}
}

// maxSeq is the last sequence number: a replica that has used them all up (2^64 - 1
// operations and reads) stops.
const maxSeq = ^uint64(0)

// do proposes one operation and waits until it is applied; it returns the key's value after
// the operation. A proposal this node drops (no leader known, or this node a leader
// transferring its leadership) is proposed again. One the leader it is forwarded to drops
// (a leader transferring its leadership) is not: do then waits forever (partial
// correctness, like Read).
func (r *KV) do(kind byte, key, val string) string {
	r.mu.Lock()
	if r.nextSeq == maxSeq {
		for {
		}
	}
	r.nextSeq++
	seq := r.nextSeq
	ch := make(chan string, 1)
	r.waiters[seq] = ch
	r.mu.Unlock()
	for r.node.Propose(context.Background(), encode(r.id, seq, kind, key, val)) != nil {
	}
	return <-ch
}

// Put sets key's value to val.
func (r *KV) Put(key, val string) {
	r.do(opPut, key, val)
}

// Get returns key's value ("" for a key never set).
func (r *KV) Get(key string) string {
	return r.do(opGet, key, "")
}

// Append appends val to key's value.
func (r *KV) Append(key, val string) {
	r.do(opAppend, key, val)
}

// TransferLeadership asks raft to hand the leadership over to replica to: if this replica is
// the leader, it makes to campaign once its log is caught up (a follower forwards the
// request to its leader, which the transport drops: deliverable). Nothing is promised of
// the outcome, and the store's operations are correct whoever leads.
func (r *KV) TransferLeadership(to uint64) {
	r.node.TransferLeadership(context.Background(), r.id, to)
}

// RemoveMember asks raft to remove replica id from the cluster's voters
// (Node.ProposeConfChange): once the change is committed, every replica's run applies it to
// its node (Node.ApplyConfChange), and the cluster's quorums are then those of the remaining
// voters; a leader that removes itself steps down (Config.StepDownOnRemoval). Nothing is
// promised of the outcome: raft drops a change proposed while another one is not yet
// applied, and RemoveMember proposes it once.
func (r *KV) RemoveMember(id uint64) {
	r.node.ProposeConfChange(context.Background(), &pb.ConfChange{Type: pb.ConfChangeRemoveNode.Enum(), NodeId: new(id)})
}

// Read returns key's value, by a read index rather than through the log: a fresh context
// (the replica and a new sequence number, like an operation's, and the key), the read
// index raft confirms for it with a quorum (Node.ReadIndex), and the key's value once the
// replica has applied the log that far. A request raft drops (no leader known) is not
// retried: Read then waits forever.
func (r *KV) Read(key string) string {
	r.mu.Lock()
	if r.nextSeq == maxSeq {
		for {
		}
	}
	r.nextSeq++
	seq := r.nextSeq
	ch := make(chan string, 1)
	r.reads[seq] = ch
	r.mu.Unlock()
	r.node.ReadIndex(context.Background(), encode(r.id, seq, opRead, key, ""))
	return <-ch
}
