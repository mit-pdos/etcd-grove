// Package kvreconf is a replicated key-value store on raft that exercises the parts of the
// library the store of examples/kv leaves out: its cluster is bootstrapped through
// configuration changes (raft.StartNode), its membership changes at random while it serves
// requests -- voters and learners added, promoted, demoted and removed, by simple changes
// (ConfChange) and by joint consensus (ConfChangeV2, with the automatic, implicit and explicit
// transitions) -- and its replicas take snapshots of their state at any configuration, compact
// their logs and catch up from one another's snapshots (a replica a partition left behind, a
// newcomer). Its network drops messages and partitions replicas, and leadership moves.
//
// What it leaves out is durability: a replica's storage is a raft.MemoryStorage, and replicas
// never crash and restart (a removed replica is stopped for good, and an id is never reused).
//
// Every Put and Get goes through the raft log; Read is a linearizable read by a read index
// (Node.ReadIndex). An operation is identified by an id the cluster gives it, so that a client
// may retry it at another replica (one that times out: a replica removed, cut off, without a
// leader) without its taking effect twice.
package kvreconf

import (
	"context"
	"encoding/binary"
	"sync"
	"time"

	"go.etcd.io/raft/v3"
	pb "go.etcd.io/raft/v3/raftpb"
	"google.golang.org/protobuf/proto"
)

const (
	opPut  = 1
	opGet  = 2
	opRead = 3
)

// encode is an operation as a log entry: its id (8 bytes, little-endian), the kind (1 byte),
// the key's length (8 bytes), the key, then the value (the rest; empty for a Get). A read's
// context (Read) is encoded the same way, with the replica's id and a sequence number of its
// own as the id (8 bytes each) in place of the operation's, of kind opRead.
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

// confCtx is the context of a configuration change the cluster proposes: its sequence
// number (8 bytes). The changes raft makes itself (the bootstrap's, the automatic leaving of
// a joint configuration) have no context.
func confCtx(seq uint64) []byte {
	b := make([]byte, 8)
	binary.LittleEndian.PutUint64(b, seq)
	return b
}

// decodeConfCtx reads back what confCtx wrote; ok is false for a change with no context.
func decodeConfCtx(b []byte) (seq uint64, ok bool) {
	if len(b) != 8 {
		return 0, false
	}
	return binary.LittleEndian.Uint64(b), true
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
// the operations applied with their answers, each as putMap writes it, then the sequence
// number of the last configuration change applied (8 bytes). The configuration itself is the
// snapshot's metadata's.
func encodeState(kv map[string]string, applied map[string]string, confSeq uint64) []byte {
	return append(putMap(putMap(nil, kv), applied), confCtx(confSeq)...)
}

// decodeState reads back what encodeState wrote; ok is false for data it did not write.
func decodeState(b []byte) (kv map[string]string, applied map[string]string, confSeq uint64, ok bool) {
	k, rest, ok1 := getMap(b)
	if !ok1 {
		return nil, nil, 0, false
	}
	a, rest2, ok2 := getMap(rest)
	if !ok2 {
		return nil, nil, 0, false
	}
	seq, ok3 := decodeConfCtx(rest2)
	if !ok3 {
		return nil, nil, 0, false
	}
	return k, a, seq, true
}

// snapEvery is the number of entries a replica applies between two of its snapshots, and
// snapMargin the number of entries below a new snapshot's index its storage keeps: both small,
// so that a replica that falls behind, or joins, is usually sent a snapshot rather than entries.
const (
	snapEvery  = 20
	snapMargin = 4
)

// Replica is one replica of the store: its id, its raft node and storage, and, under mu, its
// replicated state as of its applied index -- the store's contents, the operations applied
// (by their encoding, each with its answer: the key's value after it), the sequence number of
// the last configuration change of the cluster's it applied and the configuration -- and the
// operations and reads waiting for their answers here.
type Replica struct {
	id      uint64
	node    raft.Node
	storage *raft.MemoryStorage
	stats   *Stats
	stopc   chan struct{}

	mu       sync.Mutex
	kv       map[string]string
	applied  map[string]string
	confSeq  uint64
	cs       *pb.ConfState
	changed  bool
	index    uint64
	waiters  map[string]chan string
	nextRead uint64
	reads    map[uint64]chan string
}

// newReplica is replica id on node, a node just started on storage; send delivers the node's
// messages. It starts the replica's loop and its node's clock.
func newReplica(id uint64, node raft.Node, storage *raft.MemoryStorage, stats *Stats, send func([]*pb.Message)) *Replica {
	r := &Replica{id: id, node: node, storage: storage, stats: stats, stopc: make(chan struct{}),
		kv: make(map[string]string), applied: make(map[string]string),
		waiters: make(map[string]chan string), reads: make(map[uint64]chan string)}
	go r.run(send)
	go r.tick()
	return r
}

const tickInterval = 2 * time.Millisecond

// tick drives the node's clock until the replica stops.
func (r *Replica) tick() {
	tk := time.NewTicker(tickInterval)
	for {
		select {
		case <-tk.C:
			r.node.Tick()
		case <-r.stopc:
			tk.Stop()
			return
		}
	}
}

// stop stops the replica for good: its loop, its clock and its node.
func (r *Replica) stop() {
	close(r.stopc)
	r.node.Stop()
}

// run handles the node's Readys, in the order raft documents: install the snapshot, if any
// (in the storage, then as the replicated state: install); save the hard state and append the
// entries; send the messages; note the read states; apply the committed entries in order (a
// configuration change to the node, Node.ApplyConfChange, before the Advance that acknowledges
// it); answer the reads whose index is applied; Advance. Then, every snapEvery applied
// entries and after every configuration change it applies, it takes a snapshot of the
// replicated state at the applied index, with the configuration there (the one the last
// ApplyConfChange returned, or the installed snapshot's), and compacts the log up to
// snapMargin entries below it.
//
// The snapshot after a configuration change is needed: a leader sends a follower whose entries
// are compacted away its storage's latest snapshot, and a follower drops a snapshot whose
// configuration does not have it. A replica added after the leader's latest snapshot, once
// the log is compacted past the change that added it, would be sent that snapshot again and
// again and never catch up (and a joint configuration that needs its vote would never commit
// again, to make a newer one): issues/raft-snapshot-without-recipient-livelock.md.
func (r *Replica) run(send func([]*pb.Message)) {
	var pending []raft.ReadState
	var snapIndex uint64
	for {
		var rd raft.Ready
		select {
		case rd = <-r.node.Ready():
		case <-r.stopc:
			return
		}
		if !raft.IsEmptySnap(rd.Snapshot) {
			kv, ops, seq, ok := decodeState(rd.Snapshot.GetData())
			if !ok {
				panic("kvreconf: a snapshot whose data does not decode")
			}
			r.storage.ApplySnapshot(rd.Snapshot)
			r.install(rd.Snapshot.GetMetadata(), kv, ops, seq)
			snapIndex = rd.Snapshot.GetMetadata().GetIndex()
		}
		if !raft.IsEmptyHardState(rd.HardState) {
			r.storage.SetHardState(rd.HardState)
		}
		r.storage.Append(rd.Entries)
		send(rd.Messages)
		pending = append(pending, rd.ReadStates...)
		for _, e := range rd.CommittedEntries {
			r.applyEntry(e)
		}
		pending = r.answer(pending)
		r.node.Advance()
		r.mu.Lock()
		index := r.index
		cs := r.cs
		var data []byte
		if cs != nil && (index-snapIndex >= snapEvery || (r.changed && index > snapIndex)) {
			data = encodeState(r.kv, r.applied, r.confSeq)
			r.changed = false
		}
		r.mu.Unlock()
		if data != nil {
			if _, err := r.storage.CreateSnapshot(index, cs, data); err == nil {
				r.stats.add(&r.stats.SnapshotsTaken)
				if index > snapMargin {
					r.storage.Compact(index - snapMargin)
				}
			}
			snapIndex = index
		}
	}
}

// install replaces the replicated state by a snapshot's (its metadata and its data, decoded),
// and answers each operation waiting here that the snapshot covers -- whose entry this replica
// does not apply -- with the answer the snapshot records.
func (r *Replica) install(md *pb.SnapshotMetadata, kv map[string]string, applied map[string]string, confSeq uint64) {
	r.mu.Lock()
	r.kv = kv
	r.applied = applied
	r.confSeq = confSeq
	r.cs = proto.Clone(md.GetConfState()).(*pb.ConfState)
	r.index = md.GetIndex()
	r.changed = false
	for o, ch := range r.waiters {
		if v, done := applied[o]; done {
			delete(r.waiters, o)
			ch <- v
		}
	}
	r.mu.Unlock()
	r.stats.add(&r.stats.SnapshotsInstalled)
	if len(md.GetConfState().GetLearners()) != 0 || len(md.GetConfState().GetVotersOutgoing()) != 0 || !sameIDs(md.GetConfState().GetVoters(), initialVoters) {
		r.stats.add(&r.stats.SnapshotsReconfigured)
	}
}

// applyEntry applies one committed entry and moves the applied index to it.
func (r *Replica) applyEntry(e *pb.Entry) {
	switch e.GetType() {
	case pb.EntryNormal:
		r.applyOp(e.GetData())
	case pb.EntryConfChange:
		var cc pb.ConfChange
		if err := proto.Unmarshal(e.GetData(), &cc); err != nil {
			panic("kvreconf: a configuration change that does not decode")
		}
		r.applyConf(&cc, cc.GetContext())
	case pb.EntryConfChangeV2:
		var cc pb.ConfChangeV2
		if err := proto.Unmarshal(e.GetData(), &cc); err != nil {
			panic("kvreconf: a configuration change that does not decode")
		}
		r.applyConf(&cc, cc.GetContext())
	}
	r.mu.Lock()
	r.index = e.GetIndex()
	r.mu.Unlock()
}

// applyConf applies a committed configuration change to the node, unless it is one of the
// cluster's whose sequence number is not past the last one applied: a proposal retried (the
// cluster proposes a change again when it is not applied in time, and both copies may be
// committed), which the replica rejects by not applying it, as raft allows. Applying it again
// could be wrong (a change raft would panic on: leaving a joint configuration that is not
// one) or undo a later change. The changes raft makes itself (no context) are always applied.
func (r *Replica) applyConf(cc pb.ConfChangeI, ctx []byte) {
	seq, ours := decodeConfCtx(ctx)
	r.mu.Lock()
	stale := ours && seq <= r.confSeq
	r.mu.Unlock()
	if stale {
		r.stats.add(&r.stats.ConfChangesRejected)
		return
	}
	cs := r.node.ApplyConfChange(cc)
	r.mu.Lock()
	r.cs = cs
	r.changed = true
	if ours {
		r.confSeq = seq
	}
	r.mu.Unlock()
}

// applyOp runs one committed operation: a Put sets its key's value; either kind answers the
// operation, if it is waiting here, with the key's value after it, which the table of the
// operations applied records. An operation already applied (retried, so committed more than
// once) does not take effect again: it is answered with its recorded answer.
func (r *Replica) applyOp(data []byte) {
	_, kind, key, val, ok := decode(data)
	if !ok {
		return
	}
	o := string(data)
	r.mu.Lock()
	v, done := r.applied[o]
	if !done {
		if kind == opPut {
			r.kv[key] = val
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

// answer answers the pending reads whose index is applied with the current value of the key
// they read, and returns the others. A read nobody waits for any more (timed out) is dropped.
func (r *Replica) answer(pending []raft.ReadState) []raft.ReadState {
	var rest []raft.ReadState
	r.mu.Lock()
	for _, rs := range pending {
		if r.index < rs.Index {
			rest = append(rest, rs)
			continue
		}
		replica, seq, key, ok := decodeReadCtx(rs.RequestCtx)
		if !ok || replica != r.id {
			continue
		}
		if ch, found := r.reads[seq]; found {
			delete(r.reads, seq)
			ch <- r.kv[key]
		}
	}
	r.mu.Unlock()
	return rest
}

// propose proposes the operation op (encoded) here and waits up to timeout for its answer; ok
// is false if none came. A proposal raft drops (no leader known) is proposed again until the
// timeout. If the operation was already applied here, its answer is the recorded one.
func (r *Replica) propose(op []byte, timeout time.Duration) (string, bool) {
	o := string(op)
	ch := make(chan string, 1)
	r.mu.Lock()
	if v, done := r.applied[o]; done {
		r.mu.Unlock()
		return v, true
	}
	r.waiters[o] = ch
	r.mu.Unlock()
	ctx, cancel := context.WithTimeout(context.Background(), timeout)
	for r.node.Propose(ctx, op) != nil && ctx.Err() == nil {
		time.Sleep(tickInterval)
	}
	select {
	case v := <-ch:
		cancel()
		return v, true
	case <-ctx.Done():
		cancel()
	}
	r.mu.Lock()
	if r.waiters[o] == ch {
		delete(r.waiters, o)
	}
	r.mu.Unlock()
	select {
	case v := <-ch:
		return v, true
	default:
		return "", false
	}
}

// read reads key by a read index here, waiting up to timeout; ok is false if no answer came.
func (r *Replica) read(key string, timeout time.Duration) (string, bool) {
	ch := make(chan string, 1)
	r.mu.Lock()
	r.nextRead++
	seq := r.nextRead
	r.reads[seq] = ch
	r.mu.Unlock()
	ctx, cancel := context.WithTimeout(context.Background(), timeout)
	r.node.ReadIndex(ctx, readCtx(r.id, seq, key))
	select {
	case v := <-ch:
		cancel()
		return v, true
	case <-ctx.Done():
		cancel()
	}
	r.mu.Lock()
	delete(r.reads, seq)
	r.mu.Unlock()
	select {
	case v := <-ch:
		return v, true
	default:
		return "", false
	}
}

// state is the replica's applied index, the sequence number of the last configuration change of
// the cluster's it applied, and its configuration (nil before any).
func (r *Replica) state() (uint64, uint64, *pb.ConfState) {
	r.mu.Lock()
	defer r.mu.Unlock()
	return r.index, r.confSeq, r.cs
}

// contents is a copy of the store's contents and its applied index.
func (r *Replica) contents() (map[string]string, uint64) {
	r.mu.Lock()
	defer r.mu.Unlock()
	m := make(map[string]string)
	for k, v := range r.kv {
		m[k] = v
	}
	return m, r.index
}
