// Package register is a minimal replicated application on raft: a string-valued
// register with Put and Get, replicated by a raft Node. It is an example for
// verification: every operation, Get included, goes through the raft log, so each one
// takes effect at the point its entry is committed. Read is a linearizable read that does
// not go through the log: it asks raft for a read index (Node.ReadIndex, raft's
// ReadOnlySafe read-only queries) and answers once the replica has applied the log up to
// it.
package register

import (
	"context"
	"encoding/binary"
	"sync"

	"go.etcd.io/raft/v3"
	pb "go.etcd.io/raft/v3/raftpb"
)

const (
	opPut  = 1
	opGet  = 2
	opRead = 3
)

// encode is an operation as a log entry: the proposing replica (8 bytes, little-endian),
// its sequence number there (8 bytes), the kind (1 byte), then the value (the rest;
// empty for a Get). A read's context (Read) is encoded the same way, of kind opRead.
func encode(replica, seq uint64, kind byte, val string) []byte {
	b := make([]byte, 17, 17+len(val))
	binary.LittleEndian.PutUint64(b, replica)
	binary.LittleEndian.PutUint64(b[8:], seq)
	b[16] = kind
	return append(b, []byte(val)...)
}

// decode reads back what encode wrote; ok is false for an entry that is not an
// operation (raft's empty entries, which a new leader appends).
func decode(b []byte) (replica, seq uint64, kind byte, val string, ok bool) {
	if len(b) < 17 {
		return 0, 0, 0, "", false
	}
	return binary.LittleEndian.Uint64(b), binary.LittleEndian.Uint64(b[8:]), b[16], string(b[17:]), true
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

// InitialState is a new cluster's: no hard state (the register persists only the log's
// entries, never a HardState, so the MemoryStorage's is always empty), and the cluster's
// voters as the configuration.
func (s *Storage) InitialState() (pb.HardState, pb.ConfState, error) {
	return pb.HardState{}, pb.ConfState{Voters: s.voters}, nil
}

// Snapshot is the MemoryStorage's, but a storage that has never had one (a new
// cluster's) says it has none for now, as the Storage interface asks, rather than
// returning an empty snapshot.
func (s *Storage) Snapshot() (pb.Snapshot, error) {
	snap, err := s.MemoryStorage.Snapshot()
	if err == nil && snap.Metadata.Index == 0 {
		return snap, raft.ErrSnapshotTemporarilyUnavailable
	}
	return snap, err
}

// Register is one replica: its id, the raft node, its storage, the register's value
// as of the last applied entry, the operations applied (by their encoding), the
// operations of this replica waiting for theirs and its reads waiting for their answer
// (both by sequence number).
type Register struct {
	id      uint64
	node    raft.Node
	storage *Storage

	mu      sync.Mutex
	value   string
	nextSeq uint64
	applied map[string]bool
	waiters map[uint64]chan string
	reads   map[uint64]chan string
}

// New starts replica id on a running node and its storage; send delivers the node's
// messages to the other replicas.
func New(id uint64, node raft.Node, storage *Storage, send func([]pb.Message)) *Register {
	r := &Register{id: id, node: node, storage: storage, applied: make(map[string]bool),
		waiters: make(map[uint64]chan string), reads: make(map[uint64]chan string)}
	go r.run(send)
	return r
}

// maxIndex bounds the indices of the entries a Storage holds (the bound raft's Storage
// contract assumes of the stable log, 2^61).
const maxIndex = 1 << 61

// fits says whether appending es keeps the stored log within maxIndex.
func fits(es []pb.Entry) bool {
	return len(es) == 0 || (uint64(len(es)) <= maxIndex && es[0].Index <= maxIndex-uint64(len(es)))
}

// run handles the node's Readys: persist the entries, send the messages, note the read
// states, apply the committed entries in order, answer the reads whose index is applied,
// then Advance. A log that would outgrow maxIndex stops the replica (2^61 entries: it does
// not happen). The applied index is the number of entries applied: the log starts empty,
// at index 1, and the register takes no snapshots.
func (r *Register) run(send func([]pb.Message)) {
	var pending []raft.ReadState
	var applied uint64
	for rd := range r.node.Ready() {
		if !fits(rd.Entries) {
			for {
			}
		}
		r.storage.Append(rd.Entries)
		send(rd.Messages)
		pending = append(pending, rd.ReadStates...)
		for _, e := range rd.CommittedEntries {
			r.apply(e)
			applied++
		}
		pending = r.answer(pending, applied)
		r.node.Advance()
	}
}

// answer answers the pending reads whose index is at most applied with the current value
// (that of the log up to applied), and returns the others. A read state that is not one
// of this replica's reads waiting for its answer is dropped (raft hands out a node's read
// states only to that node, so a read's context is always its own replica's).
func (r *Register) answer(pending []raft.ReadState, applied uint64) []raft.ReadState {
	var rest []raft.ReadState
	for _, rs := range pending {
		if applied < rs.Index {
			rest = append(rest, rs)
			continue
		}
		replica, seq, kind, _, ok := decode(rs.RequestCtx)
		if !ok || replica != r.id || kind != opRead {
			continue
		}
		r.mu.Lock()
		ch, found := r.reads[seq]
		if found {
			delete(r.reads, seq)
		}
		v := r.value
		r.mu.Unlock()
		if found {
			ch <- v
		}
	}
	return rest
}

// apply runs one committed entry: a Put sets the value; either kind answers its
// waiter, if this replica proposed it, with the value after the operation. An entry
// whose operation was already applied (an operation may be committed more than once: a
// proposal retried after an error, or delivered twice) is skipped, so that an operation
// takes effect once. Operations are told apart by their encoding, which is unique: the
// replica and a sequence number of its own.
func (r *Register) apply(e pb.Entry) {
	if e.Type != pb.EntryNormal {
		return
	}
	replica, seq, kind, val, ok := decode(e.Data)
	if !ok {
		return
	}
	r.mu.Lock()
	if r.applied[string(e.Data)] {
		r.mu.Unlock()
		return
	}
	r.applied[string(e.Data)] = true
	if kind == opPut {
		r.value = val
	}
	var ch chan string
	found := false
	if replica == r.id {
		ch, found = r.waiters[seq]
		if found {
			delete(r.waiters, seq)
		}
	}
	v := r.value
	r.mu.Unlock()
	if found {
		ch <- v
	}
}

// do proposes one operation and waits until it is applied; a proposal this node drops (no
// leader known, or this node a leader transferring its leadership) is proposed again. One
// the leader it is forwarded to drops (a leader transferring its leadership) is not: do then
// waits forever (partial correctness, like Read).
func (r *Register) do(kind byte, val string) string {
	r.mu.Lock()
	r.nextSeq++
	seq := r.nextSeq
	ch := make(chan string, 1)
	r.waiters[seq] = ch
	r.mu.Unlock()
	for r.node.Propose(context.Background(), encode(r.id, seq, kind, val)) != nil {
	}
	return <-ch
}

// Put sets the register to val.
func (r *Register) Put(val string) {
	r.do(opPut, val)
}

// Get returns the register's value.
func (r *Register) Get() string {
	return r.do(opGet, "")
}

// TransferLeadership asks raft to hand the leadership over to replica to: if this replica is
// the leader, it makes to campaign once its log is caught up (a follower forwards the
// request to its leader, which the transport drops: deliverable). Nothing is promised of
// the outcome, and the register's operations are correct whoever leads.
func (r *Register) TransferLeadership(to uint64) {
	r.node.TransferLeadership(context.Background(), r.id, to)
}

// Read returns the register's value, by a read index rather than through the log: a
// fresh context (the replica and a new sequence number, like an operation's), the read
// index raft confirms for it with a quorum (Node.ReadIndex), and the value once the
// replica has applied the log that far. A request raft drops (no leader known) is not
// retried: Read then waits forever.
func (r *Register) Read() string {
	r.mu.Lock()
	r.nextSeq++
	seq := r.nextSeq
	ch := make(chan string, 1)
	r.reads[seq] = ch
	r.mu.Unlock()
	r.node.ReadIndex(context.Background(), encode(r.id, seq, opRead, ""))
	return <-ch
}
