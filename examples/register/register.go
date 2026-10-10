// Package register is a minimal replicated application on raft: a string-valued
// register with Put and Get, replicated by a raft Node. It is an example for
// verification: every operation, Get included, goes through the raft log, so each one
// takes effect at the point its entry is committed.
package register

import (
	"context"
	"encoding/binary"
	"sync"

	"go.etcd.io/raft/v3"
	pb "go.etcd.io/raft/v3/raftpb"
)

const (
	opPut = 1
	opGet = 2
)

// encode is an operation as a log entry: the proposing replica (8 bytes, little-endian),
// its sequence number there (8 bytes), the kind (1 byte), then the value (the rest;
// empty for a Get).
func encode(replica, seq uint64, kind byte, val string) []byte {
	b := make([]byte, 17, 17+len(val))
	binary.LittleEndian.PutUint64(b, replica)
	binary.LittleEndian.PutUint64(b[8:], seq)
	b[16] = kind
	return append(b, val...)
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

// InitialState is the MemoryStorage's, with the cluster's voters as the configuration.
func (s *Storage) InitialState() (pb.HardState, pb.ConfState, error) {
	hs, _, err := s.MemoryStorage.InitialState()
	return hs, pb.ConfState{Voters: append([]uint64(nil), s.voters...)}, err
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
// as of the last applied entry, the last sequence number applied of each replica, and
// the operations of this replica waiting for theirs (by sequence number).
type Register struct {
	id      uint64
	node    raft.Node
	storage *Storage

	mu      sync.Mutex
	value   string
	nextSeq uint64
	applied map[uint64]uint64
	waiters map[uint64]chan string
}

// New starts replica id on a running node and its storage; send delivers the node's
// messages to the other replicas.
func New(id uint64, node raft.Node, storage *Storage, send func([]pb.Message)) *Register {
	r := &Register{id: id, node: node, storage: storage, applied: make(map[uint64]uint64), waiters: make(map[uint64]chan string)}
	go r.run(send)
	return r
}

// run handles the node's Readys: persist the entries, send the messages, apply the
// committed entries in order, then Advance.
func (r *Register) run(send func([]pb.Message)) {
	for rd := range r.node.Ready() {
		r.storage.Append(rd.Entries)
		send(rd.Messages)
		for _, e := range rd.CommittedEntries {
			r.apply(e)
		}
		r.node.Advance()
	}
}

// apply runs one committed entry: a Put sets the value; either kind answers its
// waiter, if this replica proposed it, with the value after the operation. An entry
// whose operation was already applied (one replica's operations are proposed one at a
// time, in sequence order) is skipped, so that an operation takes effect once.
func (r *Register) apply(e pb.Entry) {
	if e.Type != pb.EntryNormal {
		return
	}
	replica, seq, kind, val, ok := decode(e.Data)
	if !ok {
		return
	}
	r.mu.Lock()
	if seq <= r.applied[replica] {
		r.mu.Unlock()
		return
	}
	r.applied[replica] = seq
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

// do proposes one operation and waits until it is applied; a dropped proposal (no
// leader known) is proposed again.
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
