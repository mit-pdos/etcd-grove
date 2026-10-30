// Package durablekv is the replicated key-value store of examples/kv (Put, Get, Append, every
// operation through the raft log) made durable: a replica keeps its raft state -- the hard
// state, the log and the latest snapshot, which holds the store's contents -- in one file of
// the durable package, rewritten whole whenever the state changes and before the replica sends
// the messages that depend on it, as raft asks. A replica that crashes (Cluster.Restart) loses
// everything else; it restarts from its file and replays its log.
//
// Durability uses nothing but whole-file reads and writes (package durable, the Go side of the
// GooseLang extension durableExt), with no write-ahead log: the file is small because the log
// is compacted behind a snapshot every snapEvery entries.
//
// An operation is identified by its encoding (encode), which a client chooses unique (Cluster:
// an epoch it keeps durably and a sequence number), and takes effect once however often it is
// proposed: a client whose replica crashes, or that waits too long, proposes it again, and the
// replicas answer a repeat with the answer recorded for the first (the operations applied, part
// of the replicated state and so of the snapshots).
package durablekv

import (
	"context"
	"encoding/binary"
	"sync"

	"github.com/mit-pdos/etcd-grove/examples/durable"
	"go.etcd.io/raft/v3"
	pb "go.etcd.io/raft/v3/raftpb"
)

const (
	opPut    = 1
	opGet    = 2
	opAppend = 3
)

// encode is an operation as a log entry: the client's epoch (8 bytes, little-endian), its
// sequence number in the epoch (8 bytes), the kind (1 byte), the key's length (8 bytes), the
// key, then the value (the rest; empty for a Get).
func encode(epoch, seq uint64, kind byte, key, val string) []byte {
	b := make([]byte, 25, 25+len(key)+len(val))
	binary.LittleEndian.PutUint64(b, epoch)
	binary.LittleEndian.PutUint64(b[8:], seq)
	b[16] = kind
	binary.LittleEndian.PutUint64(b[17:], uint64(len(key)))
	b = append(b, []byte(key)...)
	return append(b, []byte(val)...)
}

// decode reads back the kind, key and value encode wrote; ok is false for an entry that is not
// an operation (raft's empty entries, which a new leader appends).
func decode(b []byte) (kind byte, key, val string, ok bool) {
	if len(b) < 25 {
		return 0, "", "", false
	}
	n := binary.LittleEndian.Uint64(b[17:])
	if uint64(len(b)-25) < n {
		return 0, "", "", false
	}
	return b[16], string(b[25 : 25+n]), string(b[25+n:]), true
}

// maxIndex bounds the indices of the entries a Storage holds (the bound raft's Storage
// contract assumes of the stable log, 2^61).
const maxIndex = 1 << 61

// snapEvery is the number of entries a replica applies between two of its snapshots, and
// snapMargin the number of entries below a new snapshot's index its storage keeps, so that a
// follower a little behind is still sent entries rather than the snapshot.
const (
	snapEvery  = 100
	snapMargin = 10
)

// fits says whether appending es keeps the stored log within maxIndex.
func fits(es []*pb.Entry) bool {
	return len(es) == 0 || (uint64(len(es)) <= maxIndex && es[0].GetIndex() <= maxIndex-uint64(len(es)))
}

// Replica is one incarnation of a replica: its id, its durable file, the raft node, its
// storage, the store's contents as of the last applied entry, the operations applied (by their
// encoding, each with its key's value right after it: what the operation answers) and the
// operations waiting for theirs (by encoding). An incarnation ends when it crashes (crash):
// it then writes its file no more, and its run stops.
type Replica struct {
	id      uint64
	file    string
	node    raft.Node
	storage *Storage

	mu      sync.Mutex
	kv      map[string]string
	applied map[string]string
	waiters map[string]chan string

	// fileMu orders the file's writes with the crash: once crashed is set, nothing writes the
	// file, so the next incarnation reads what this one last wrote.
	fileMu  sync.Mutex
	crashed bool
	// done is closed when the incarnation crashes.
	done chan struct{}
}

// start starts an incarnation of replica id from its file (a new replica of the cluster of
// voters if there is none): its storage as the file left it, its node restarted on it, and
// the store's contents and operations applied from the storage's snapshot, if any; the
// entries after the snapshot are replayed as raft hands them back as committed. send
// delivers the node's messages to the other replicas.
func start(id uint64, file string, voters []uint64, send func([]*pb.Message)) *Replica {
	data, ok := durable.Read(file)
	st, good := OpenStorage(voters, data, ok)
	if !good {
		// a file this package did not write
		for {
		}
	}
	snap, _ := st.Snapshot()
	kv, ops, good2 := decodeState(snap.GetData())
	if !good2 {
		for {
		}
	}
	applied := snap.GetMetadata().GetIndex()
	node := raft.RestartNode(&raft.Config{
		ID:              id,
		ElectionTick:    10,
		HeartbeatTick:   1,
		Storage:         st,
		Applied:         applied,
		MaxSizePerMsg:   1 << 20,
		MaxInflightMsgs: 256,
		Logger:          quietLogger{},
	})
	r := &Replica{id: id, file: file, node: node, storage: st, kv: kv, applied: ops,
		waiters: make(map[string]chan string), done: make(chan struct{})}
	go r.run(send, applied)
	return r
}

// crash ends the incarnation: it writes its file no more, its waiters are told (done), and
// its node stops.
func (r *Replica) crash() {
	r.fileMu.Lock()
	r.crashed = true
	r.fileMu.Unlock()
	close(r.done)
	r.node.Stop()
}

// persist writes the storage to the file; false if the incarnation has crashed, which then
// writes nothing.
func (r *Replica) persist() bool {
	data := r.storage.Encode()
	r.fileMu.Lock()
	ok := !r.crashed
	if ok {
		durable.Write(r.file, string(data))
	}
	r.fileMu.Unlock()
	return ok
}

// run handles the node's Readys until the incarnation crashes; applied is the index of the
// last entry its state reflects (its snapshot's).
func (r *Replica) run(send func([]*pb.Message), applied uint64) {
	for {
		select {
		case rd := <-r.node.Ready():
			next, ok := r.handle(rd, send, applied)
			if !ok {
				return
			}
			applied = next
		case <-r.done:
			return
		}
	}
}

// handle handles one Ready: install the snapshot, if any, store the hard state and the
// entries, and write the storage to the file if any of them changed it -- all before sending
// the messages, which may promise what they record (a vote, an acknowledged entry) -- then
// apply the committed entries in order and Advance. Every snapEvery applied entries, the
// replica takes a snapshot of its state at the applied index, compacts its log up to
// snapMargin entries below it and writes the file again. It returns the applied index after
// the Ready, and false if the incarnation has crashed (it then sends nothing more). A log that
// would outgrow maxIndex, or a snapshot whose data does not decode (every snapshot is a
// replica's, encodeState's), stops the replica: neither happens.
//
// A Ready's snapshot (one of another replica's, which this one lags too far behind to be sent
// entries) replaces the store's contents and the operations applied (install), and the applied
// index jumps to its index.
func (r *Replica) handle(rd raft.Ready, send func([]*pb.Message), applied uint64) (uint64, bool) {
	if !fits(rd.Entries) {
		for {
		}
	}
	changed := false
	if rd.Snapshot != nil {
		kv, ops, ok := decodeState(rd.Snapshot.GetData())
		if !ok {
			for {
			}
		}
		r.install(kv, ops)
		applied = rd.Snapshot.GetMetadata().GetIndex()
		r.storage.ApplySnapshot(rd.Snapshot)
		changed = true
	}
	if !raft.IsEmptyHardState(rd.HardState) {
		r.storage.SetHardState(rd.HardState)
		changed = true
	}
	if len(rd.Entries) != 0 {
		r.storage.Append(rd.Entries)
		changed = true
	}
	if changed && !r.persist() {
		return applied, false
	}
	send(rd.Messages)
	snapIndex := r.storage.SnapshotIndex()
	for _, e := range rd.CommittedEntries {
		r.apply(e)
		applied++
	}
	r.node.Advance()
	if applied-snapIndex >= snapEvery {
		r.mu.Lock()
		data := encodeState(r.kv, r.applied)
		r.mu.Unlock()
		r.storage.CreateSnapshot(applied, &pb.ConfState{Voters: r.storage.voters}, data)
		if applied > snapMargin {
			r.storage.Compact(applied - snapMargin)
		}
		if !r.persist() {
			return applied, false
		}
	}
	return applied, true
}

// install replaces the store's contents and the operations applied by a snapshot's (decoded,
// decodeState), and answers each operation waiting for its answer that the snapshot covers
// (whose entry this replica does not apply) with the answer the snapshot records.
func (r *Replica) install(kv map[string]string, applied map[string]string) {
	r.mu.Lock()
	r.kv = kv
	r.applied = applied
	for o, v := range applied {
		ch, found := r.waiters[o]
		if found {
			delete(r.waiters, o)
			ch <- v
		}
	}
	r.mu.Unlock()
}

// apply runs one committed entry: a Put sets its key's value, an Append appends to it; any
// kind records its answer, the key's value after the operation, and answers its waiter, if
// any. An entry whose operation was already applied (a proposal retried) changes nothing and
// answers its waiter with the answer recorded, so that an operation takes effect once.
func (r *Replica) apply(e *pb.Entry) {
	if e.GetType() != pb.EntryNormal {
		return
	}
	kind, key, val, ok := decode(e.GetData())
	if !ok {
		return
	}
	o := string(e.GetData())
	r.mu.Lock()
	v, done := r.applied[o]
	if !done {
		if kind == opPut {
			r.kv[key] = val
		} else if kind == opAppend {
			r.kv[key] = r.kv[key] + val
		}
		v = r.kv[key]
		r.applied[o] = v
	}
	ch, found := r.waiters[o]
	if found {
		delete(r.waiters, o)
	}
	r.mu.Unlock()
	if found {
		ch <- v
	}
}

// propose proposes the operation o to this incarnation and returns a channel of its answer,
// or nil if the node drops the proposal (no leader known, or the incarnation crashed). The
// channel is answered once, unless the incarnation crashes or the proposal is lost (a leader
// that crashes before it replicates it): the caller then proposes again.
func (r *Replica) propose(o []byte) chan string {
	ch := make(chan string, 1)
	r.mu.Lock()
	r.waiters[string(o)] = ch
	r.mu.Unlock()
	if r.node.Propose(context.Background(), o) != nil {
		r.mu.Lock()
		if r.waiters[string(o)] == ch {
			delete(r.waiters, string(o))
		}
		r.mu.Unlock()
		return nil
	}
	return ch
}
