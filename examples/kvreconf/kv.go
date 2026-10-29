// Package kvreconf is a replicated key-value store on raft whose test program is meant to be
// read as a specification of how an application may use raft: every choice the application is
// allowed to make is made at random (primitive.RandomUint64), so that the program's possible
// executions include every interleaving of the store's requests with snapshots and
// configuration changes.
//
//   - Snapshots: after any applied entry or Ready, a replica may take a snapshot of its state at
//     its applied index (with the configuration there), and may compact its log to any index
//     raft allows (at most its latest snapshot's and its acknowledged applied index); its storage
//     may answer, when raft asks for a snapshot to send, that none is available for now.
//   - Configuration changes: proposers propose random changes at random times through random
//     replicas -- simple and joint (ConfChange and ConfChangeV2, every transition, the explicit
//     leaving of a joint configuration), of voters and learners, of members, of replicas removed
//     earlier and of new ones -- concurrently with one another, with no regard for what is
//     pending. A replica applies a committed change only if it is valid on its current
//     configuration (raft's own confchange rules, Replica.applyConf), and rejects it otherwise
//     (raft lets an application reject a change by not applying it): the replicas apply the same
//     log, so they all reject the same changes.
//   - The network drops, duplicates, delays and reorders messages; leadership is transferred,
//     campaigns started and leaders forgotten at random; raft's options are chosen at random.
//
// What it leaves out is durability: a replica's storage is a raft.MemoryStorage, and replicas
// never crash or restart. A removed replica keeps running (it may be added back, with its old
// log); a new one starts empty (raft.RestartNode on an empty storage) and catches up from the
// leader's log or snapshot.
//
// Every Put and Get goes through the raft log; Read is a linearizable read by a read index
// (Node.ReadIndex). An operation is identified by an id the cluster gives it, so that a client
// may retry it at another replica without its taking effect twice.
package kvreconf

import (
	"context"
	"encoding/binary"
	"sync"
	"time"

	"github.com/goose-lang/primitive"
	"go.etcd.io/raft/v3"
	"go.etcd.io/raft/v3/confchange"
	pb "go.etcd.io/raft/v3/raftpb"
	"go.etcd.io/raft/v3/tracker"
	"google.golang.org/protobuf/proto"
)

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
// context (Read) is encoded the same way, after the replica's id (8 bytes), with a sequence
// number of the replica's as the id, of kind opRead.
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
	// the configurations the protocol admits have fewer than 2^62 members (never reached here, with
	// at most maxReplicas of them, but checked so that a change it accepts is one raft's protocol
	// allows: the store's decision on a committed conf entry, the same at every replica)
	return err == nil && uint64(len(after)) < 1<<62
}

// maxIndex bounds the indices of the entries a Storage holds (the bound raft's Storage contract
// assumes of the stable log, 2^61): a replica stops before its log outgrows it (run).
const maxIndex = 1 << 61

// fits says whether appending es keeps the stored log within maxIndex.
func fits(es []*pb.Entry) bool {
	return len(es) == 0 || (uint64(len(es)) <= maxIndex && es[0].GetIndex() <= maxIndex-uint64(len(es)))
}

// maxSeq is the last operation id and read sequence number: a cluster that has used up its
// operation ids (Cluster.do), or a replica its read sequence numbers (read), stops issuing them,
// so that an id is never reused (a reused one would be answered with another operation's
// answer). 2^64 - 1 of them: it does not happen.
const maxSeq = ^uint64(0)

// Storage is a replica's raft storage: a MemoryStorage that, when raft asks for its snapshot
// (to send to a follower), may answer at random that none is available for now, as the Storage
// interface allows (raft then asks again later); and that answers InitialState with the bootstrap
// configuration (`boot`), so that every replica, a founder or a newcomer, starts at it and replays
// the same configurations from the log.
type Storage struct {
	*raft.MemoryStorage
	boot *pb.ConfState
}

// InitialState is the MemoryStorage's hard state, with the bootstrap configuration.
func (s *Storage) InitialState() (*pb.HardState, *pb.ConfState, error) {
	hs, _, err := s.MemoryStorage.InitialState()
	return hs, proto.Clone(s.boot).(*pb.ConfState), err
}

// Snapshot is the MemoryStorage's, or, one time in four, ErrSnapshotTemporarilyUnavailable.
func (s *Storage) Snapshot() (*pb.Snapshot, error) {
	if oneIn(4) {
		return nil, raft.ErrSnapshotTemporarilyUnavailable
	}
	return s.MemoryStorage.Snapshot()
}

// Replica is one replica of the store: its id, its raft node and storage, and, under mu, its
// replicated state as of its applied index -- the store's contents, the operations applied
// (by their encoding, each with its answer: the key's value after it) and the configuration --
// and the operations and reads waiting for their answers here.
type Replica struct {
	id      uint64
	node    raft.Node
	storage *Storage
	stats   *Stats
	tick    time.Duration
	stopc   chan struct{}
	// runDone and tickDone each get one value, when run and ticker return (stop waits for them)
	runDone  chan struct{}
	tickDone chan struct{}

	mu       sync.Mutex
	kv       map[string]string
	applied  map[string]string
	cs       *pb.ConfState
	index    uint64
	waiters  map[string]chan string
	nextRead uint64
	reads    map[uint64]chan string
}

// newReplica is replica id on node, a node just started on storage at the configuration cs0, ticked
// every tick; send delivers the node's messages. It starts the replica's loop and its node's clock.
func newReplica(id uint64, node raft.Node, storage *Storage, cs0 *pb.ConfState, tick time.Duration, stats *Stats, send func([]*pb.Message)) *Replica {
	r := &Replica{id: id, node: node, storage: storage, stats: stats, tick: tick, stopc: make(chan struct{}),
		runDone: make(chan struct{}, 1), tickDone: make(chan struct{}, 1),
		cs: proto.Clone(cs0).(*pb.ConfState),
		kv: make(map[string]string), applied: make(map[string]string),
		waiters: make(map[string]chan string), reads: make(map[uint64]chan string)}
	go r.run(send)
	go r.ticker()
	return r
}

// ticker drives the node's clock until the replica stops.
func (r *Replica) ticker() {
	tk := time.NewTicker(r.tick)
	for {
		select {
		case <-tk.C:
			r.node.Tick()
		case <-r.stopc:
			tk.Stop()
			r.tickDone <- struct{}{}
			return
		}
	}
}

// stop stops the replica for good: its loop, its clock and its node. It stops the node only once
// the loop and the clock have returned, so that the loop never meets a stopped node: every call it
// makes (the Ready, ApplyConfChange, Advance) is on a running one. (Other goroutines -- proposers,
// readers, the network's Step -- may still call a stopped node; they handle its answers.)
func (r *Replica) stop() {
	close(r.stopc)
	<-r.runDone
	<-r.tickDone
	r.node.Stop()
}

// run handles the node's Readys, in the order raft documents: install the snapshot, if any
// (in the storage, then as the replicated state: install); save the hard state and append the
// entries; send the messages; note the read states; apply the committed entries in order (a
// configuration change to the node, Node.ApplyConfChange, before the Advance that acknowledges
// it); answer the reads whose index is applied; Advance. A Ready whose entries would take the
// log past maxIndex stops the loop (it does not happen).
//
// Snapshots and compaction are the application's to choose: after any entry it applies and
// after any Advance, the replica may take a snapshot (maybeSnapshot), and after any Advance it
// may compact its log to any index from its first one to the least of its latest snapshot's
// (compacting past it, the leader would have no snapshot to send a follower that needs the
// compacted entries: issues/raft-compact-past-snapshot.md) and its applied index as raft knows
// it (the bound MemoryStorage.Compact documents: what it applied before the last Advance).
func (r *Replica) run(send func([]*pb.Message)) {
	var pending []raft.ReadState
	var snapIndex uint64
	for {
		var rd raft.Ready
		select {
		case rd = <-r.node.Ready():
		case <-r.stopc:
			r.runDone <- struct{}{}
			return
		}
		if !fits(rd.Entries) {
			// a log of 2^61 entries: it does not happen
			r.runDone <- struct{}{}
			return
		}
		if !raft.IsEmptySnap(rd.Snapshot) {
			kv, ops, ok := decodeState(rd.Snapshot.GetData())
			if !ok {
				panic("kvreconf: a snapshot whose data does not decode")
			}
			r.storage.ApplySnapshot(rd.Snapshot)
			r.install(rd.Snapshot.GetMetadata(), kv, ops)
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
			if oneIn(8) {
				snapIndex = r.maybeSnapshot(snapIndex)
			}
		}
		pending = r.answer(pending)
		r.node.Advance()
		if oneIn(4) {
			snapIndex = r.maybeSnapshot(snapIndex)
		}
		if oneIn(4) {
			r.maybeCompact(snapIndex)
		}
	}
}

// maybeSnapshot takes a snapshot of the replicated state at the applied index, with the
// configuration there, unless the latest snapshot is already that recent (or no configuration
// is applied yet: a new replica's, before it catches up); it returns the latest snapshot's index.
func (r *Replica) maybeSnapshot(snapIndex uint64) uint64 {
	r.mu.Lock()
	index := r.index
	cs := r.cs
	var data []byte
	if cs != nil && index > snapIndex {
		data = encodeState(r.kv, r.applied)
	}
	r.mu.Unlock()
	if data == nil {
		return snapIndex
	}
	if _, err := r.storage.CreateSnapshot(index, cs, data); err != nil {
		panic("kvreconf: CreateSnapshot: " + err.Error())
	}
	r.stats.add(&r.stats.SnapshotsTaken)
	if len(cs.GetVotersOutgoing()) != 0 {
		r.stats.add(&r.stats.SnapshotsTakenJoint)
	}
	return index
}

// maybeCompact compacts the log to a random index allowed after an Advance (run), if there is
// one past the first.
func (r *Replica) maybeCompact(snapIndex uint64) {
	first, _ := r.storage.FirstIndex()
	r.mu.Lock()
	hi := r.index
	r.mu.Unlock()
	if snapIndex < hi {
		hi = snapIndex
	}
	if hi < first {
		return
	}
	if err := r.storage.Compact(first + below(hi-first+1)); err == nil {
		r.stats.add(&r.stats.Compactions)
	}
}

// install replaces the replicated state by a snapshot's (its metadata and its data, decoded),
// and answers each operation waiting here that the snapshot covers -- whose entry this replica
// does not apply -- with the answer the snapshot records.
func (r *Replica) install(md *pb.SnapshotMetadata, kv map[string]string, applied map[string]string) {
	cs := proto.Clone(md.GetConfState()).(*pb.ConfState)
	r.mu.Lock()
	r.kv = kv
	r.applied = applied
	r.cs = cs
	r.index = md.GetIndex()
	for o, ch := range r.waiters {
		if v, done := applied[o]; done {
			delete(r.waiters, o)
			ch <- v
		}
	}
	r.mu.Unlock()
	r.stats.add(&r.stats.SnapshotsInstalled)
	if len(cs.GetVotersOutgoing()) != 0 {
		r.stats.add(&r.stats.SnapshotsInstalledJoint)
	}
	if len(cs.GetLearners()) != 0 || len(cs.GetLearnersNext()) != 0 {
		r.stats.add(&r.stats.SnapshotsInstalledLearners)
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
		r.applyConf(&cc)
	case pb.EntryConfChangeV2:
		var cc pb.ConfChangeV2
		if err := proto.Unmarshal(e.GetData(), &cc); err != nil {
			panic("kvreconf: a configuration change that does not decode")
		}
		r.applyConf(&cc)
	}
	r.mu.Lock()
	r.index = e.GetIndex()
	r.mu.Unlock()
}

// applyConf applies a committed configuration change to the node if it is valid on the
// current configuration (validConf), and rejects it otherwise by not applying it, as raft
// allows (applying it, raft would panic). The proposers propose any change at any time, so a
// change committed may be invalid by the time it is applied (made so by changes committed
// before it); every replica applies the same entries from the same configuration, so they all
// decide the same.
func (r *Replica) applyConf(cc pb.ConfChangeI) {
	v2 := cc.AsV2()
	r.mu.Lock()
	cur := r.cs
	r.mu.Unlock()
	if !validConf(cur, v2) {
		r.stats.add(&r.stats.ConfChangesRejected)
		return
	}
	cs := r.node.ApplyConfChange(cc)
	r.mu.Lock()
	r.cs = cs
	r.mu.Unlock()
	r.stats.add(&r.stats.ConfChangesApplied)
	if _, joint := v2.EnterJoint(); joint {
		r.stats.add(&r.stats.JointEntered)
	}
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
		time.Sleep(time.Millisecond)
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

// read reads key by a read index here, waiting up to timeout; ok is false if no answer came (or
// the replica's read sequence numbers are used up: maxSeq).
func (r *Replica) read(key string, timeout time.Duration) (string, bool) {
	ch := make(chan string, 1)
	r.mu.Lock()
	if r.nextRead == maxSeq {
		r.mu.Unlock()
		return "", false
	}
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

// conf is the replica's configuration (nil before any) and its applied index.
func (r *Replica) conf() (*pb.ConfState, uint64) {
	r.mu.Lock()
	defer r.mu.Unlock()
	return r.cs, r.index
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
