package kvnet

import (
	"time"

	"sync"

	"github.com/mit-pdos/etcd-grove/examples/lib/durable"
	"go.etcd.io/raft/v3"
	pb "go.etcd.io/raft/v3/raftpb"
)

// Replica is the replica a process runs: kvdurable's Replica (examples/raft/kvdurable/kv.go)
// with the process as its incarnation. Its id, its durable file, its raft node and storage, and,
// under mu, its replicated state as of its applied index -- the store's contents, the operations
// applied (by their encoding, each with its answer: the key's value after it) and the
// configuration -- and the operations and reads waiting for their answers here.
//
// An incarnation ends when its process is killed, or its machine loses power, and nothing it does
// then (a write half done, a message half sent) needs the program's help; or when it is stopped
// (stop: Node.restart, at a client's request), and the process starts the next incarnation from
// the file. Unlike kvdurable's, it never crashes itself (a crash is the machine's), so it has no
// crashed flag; the read sequence numbers come from the clients (a read's context outlives the
// incarnation that issued it: the clients never reuse a number, kvdurable's readSeqs).
type Replica struct {
	id      uint64
	file    string
	node    raft.Node
	storage *Storage
	stats   *Stats
	tick    time.Duration
	stopc   chan struct{}
	// snapc carries run's requests to the snapshot goroutine (snapshotter), one at most at a time
	snapc chan snapReq
	// runDone, tickDone and snapDone each get one value, when run, ticker and snapshotter return
	// (stop waits for them)
	runDone  chan struct{}
	tickDone chan struct{}
	snapDone chan struct{}

	// dmu orders the storage's changes and the file's writes: each group of changes (a Ready's, a
	// snapshot, a compaction: each to the MemoryStorage and to its image, Storage.img) and each
	// write (persist, of the image) holds it, so that a write is of the contents between two
	// groups.
	dmu sync.Mutex

	mu      sync.Mutex
	kv      map[string]string
	applied map[string]string
	cs      *pb.ConfState
	index   uint64
	waiters map[string]chan string
	reads   map[uint64]chan string
}

// newReplica is the replica id on node, a node just started on storage, whose durable file is
// file, at the replicated state (kv, applied, cs) of index (its storage's snapshot's: 0 and the
// bootstrap configuration if it has none), raft's applied index at start rafted
// (Config.Applied, or the log's start if that is 0), ticked every tick; send hands the node's
// messages to the network. It starts the replica's loop, its node's clock and its snapshot
// goroutine.
func newReplica(id uint64, file string, node raft.Node, storage *Storage, kv map[string]string, applied map[string]string,
	cs *pb.ConfState, index uint64, rafted uint64, tick time.Duration, stats *Stats,
	send func([]*pb.Message)) *Replica {
	hs := storage.img.hs
	r := &Replica{id: id, file: file, node: node, storage: storage, stats: stats, tick: tick, stopc: make(chan struct{}),
		snapc:   make(chan snapReq, 1),
		runDone: make(chan struct{}, 1), tickDone: make(chan struct{}, 1), snapDone: make(chan struct{}, 1),
		cs: pb.CloneConfState(cs), index: index,
		kv: kv, applied: applied,
		waiters: make(map[string]chan string), reads: make(map[uint64]chan string)}
	go r.run(send, index, hs, rafted)
	go r.ticker()
	go r.snapshotter(index)
	return r
}

// ticker drives the node's clock until the incarnation stops.
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

// stop stops the incarnation for good, as kvdurable's Replica.stop: its loop, its clock, its
// snapshot goroutine and its node. It stops the node only once the loop and the clock have
// returned, so that the loop never meets a stopped node: every call it makes (the Ready,
// ApplyConfChange, Advance) is on a running one. (Other goroutines -- proposers, readers, the
// transport -- may still call a stopped node; they handle its answers.) Once run and the snapshot
// goroutine have returned, nothing writes the file: the last critical section of dmu does nothing
// at run time, and lets the proof take the file's writer out of dmu's invariant for the next
// incarnation.
func (r *Replica) stop() {
	close(r.stopc)
	<-r.runDone
	<-r.tickDone
	<-r.snapDone
	r.node.Stop()
	r.dmu.Lock()
	r.dmu.Unlock()
}

// persist writes the storage's image to the file.
func (r *Replica) persist() {
	r.dmu.Lock()
	durable.Write(r.file, string(r.storage.encode()))
	r.stats.add(StFileWrites)
	r.dmu.Unlock()
}

// run handles the node's Readys, as kvdurable's Replica.run does: install the snapshot, if any
// (in the storage and its image, then as the replicated state: install); save the hard state
// and append the entries (in both); write the image to the file if raft needs it durable, and
// send the messages; note the read states; apply the committed entries in order (a
// configuration change to the node, Node.ApplyConfChange, before the Advance that acknowledges
// it); answer the reads whose index is applied; Advance. A Ready whose entries would take the
// log past maxIndex stops the loop (it does not happen).
//
// Durability, as kvdurable's: a Ready that installs a snapshot, appends entries or changes the
// term or the vote (raft.MustSync) is written before its messages are sent -- except at a
// replica whose last reported role is leader, which may send them first, one time in two, as
// etcd does -- and always before it is applied and Advanced; one that changes only the commit
// index is written one time in two; one that changes nothing is not written. Sending here is
// handing the messages to the transport (send), which writes them to the network from other
// goroutines: a message may reach its target after a later write of this replica, or never.
//
// Snapshots and compaction are asked of the snapshot goroutine (request), as in kvdurable. It
// returns when the incarnation stops (stop), between two Readys.
func (r *Replica) run(send func([]*pb.Message), snapIndex uint64, hs *pb.HardState, rafted uint64) {
	var pending []raft.ReadState
	lead := false
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
		if rd.SoftState != nil {
			lead = rd.SoftState.RaftState == raft.StateLeader
		}
		snap := !raft.IsEmptySnap(rd.Snapshot)
		var kv, ops map[string]string
		if snap {
			k, o, ok := decodeState(rd.Snapshot.GetData())
			if !ok {
				panic("kvnet: a snapshot whose data does not decode")
			}
			kv, ops = k, o
		}
		changed := !raft.IsEmptyHardState(rd.HardState)
		sync := snap || len(rd.Entries) != 0 || (changed && raft.MustSync(rd.HardState, hs, 0))
		r.dmu.Lock()
		if snap {
			r.storage.ApplySnapshot(rd.Snapshot)
		}
		if changed {
			r.storage.SetHardState(rd.HardState)
			hs = rd.HardState
		}
		r.storage.Append(rd.Entries)
		r.dmu.Unlock()
		if snap {
			r.install(rd.Snapshot.GetMetadata(), kv, ops)
			snapIndex = rd.Snapshot.GetMetadata().GetIndex()
			rafted = snapIndex
		}
		write := sync
		if !sync && changed {
			if oneIn(2) {
				write = true
			} else {
				r.stats.add(StCommitUnwritten)
			}
		}
		first := lead && sync && oneIn(2)
		if first {
			r.stats.add(StLeaderSentFirst)
			send(rd.Messages)
		}
		if write {
			r.persist()
		}
		if !first {
			send(rd.Messages)
		}
		pending = append(pending, rd.ReadStates...)
		for _, e := range rd.CommittedEntries {
			r.applyEntry(e)
			rafted = e.GetIndex()
			if oneIn(8) {
				snapIndex = r.request(snapIndex, true, 0)
			}
		}
		pending = r.answer(pending)
		r.node.Advance()
		bound := uint64(0)
		if oneIn(4) {
			bound = rafted
		}
		snapIndex = r.request(snapIndex, oneIn(4), bound)
	}
}

// snapReq is a request of run to the snapshot goroutine: a snapshot at index of the configuration
// cs and the encoded replicated state data, unless data is nil; a compaction up to compact, unless
// it is 0.
type snapReq struct {
	index   uint64
	cs      *pb.ConfState
	data    []byte
	compact uint64
}

// request is kvdurable's Replica.request: it asks the snapshot goroutine, without waiting, for a
// snapshot of the replicated state at the applied index if snap (unless the latest one asked for
// is already that recent, or no configuration is applied yet), and for a compaction up to the
// least of the applied index and bound, unless bound is 0; a request is dropped if the goroutine
// has one pending. It returns the index of the latest snapshot asked for.
func (r *Replica) request(snapIndex uint64, snap bool, bound uint64) uint64 {
	r.mu.Lock()
	index := r.index
	cs := r.cs
	var data []byte
	if snap && cs != nil && index > snapIndex {
		data = encodeState(r.kv, r.applied)
	}
	r.mu.Unlock()
	req := snapReq{index: index, cs: cs, data: data}
	req.compact = bound
	if index < bound {
		req.compact = index
	}
	if data == nil && req.compact == 0 {
		return snapIndex
	}
	select {
	case r.snapc <- req:
		if data != nil {
			return index
		}
	default:
	}
	return snapIndex
}

// snapshotter takes the snapshots and makes the compactions run asks for, until the incarnation
// stops; known is the least index the stored snapshot is known to have reached (the storage's at
// start).
func (r *Replica) snapshotter(known uint64) {
	for {
		select {
		case req := <-r.snapc:
			known = r.snapshot(req, known)
		case <-r.stopc:
			r.snapDone <- struct{}{}
			return
		}
	}
}

// snapshot is kvdurable's Replica.snapshot: it takes the snapshot (in the storage and its
// image), which may be out of date (ErrSnapOutOfDate), and compacts the log (in both) to a random
// index from its first one to the least of the requested bound and the stored snapshot's index as
// known, if there is one. Neither needs to be durable: it writes the image to the file afterwards
// one time in two. It returns what is known of the stored snapshot's index after it.
func (r *Replica) snapshot(req snapReq, known uint64) uint64 {
	changed := false
	if req.data != nil {
		r.dmu.Lock()
		err := r.storage.CreateSnapshot(req.index, req.cs, req.data)
		r.dmu.Unlock()
		if err == nil {
			changed = true
			r.stats.add(StSnapshotsTaken)
			if len(req.cs.GetVotersOutgoing()) != 0 {
				r.stats.add(StSnapshotsTakenJoint)
			}
		} else if err != raft.ErrSnapOutOfDate {
			panic("kvnet: CreateSnapshot: " + err.Error())
		}
		if known < req.index {
			known = req.index
		}
	}
	if req.compact != 0 {
		first, _ := r.storage.FirstIndex()
		hi := req.compact
		if known < hi {
			hi = known
		}
		if hi >= first {
			r.dmu.Lock()
			err := r.storage.Compact(first + below(hi-first+1))
			r.dmu.Unlock()
			if err == nil {
				changed = true
				r.stats.add(StCompactions)
			}
		}
	}
	if changed && oneIn(2) {
		r.persist()
	}
	return known
}

// install replaces the replicated state by a snapshot's (its metadata and its data, decoded),
// and answers each operation waiting here that the snapshot covers with the answer the snapshot
// records.
func (r *Replica) install(md *pb.SnapshotMetadata, kv map[string]string, applied map[string]string) {
	cs := pb.CloneConfState(md.GetConfState())
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
	r.stats.add(StSnapshotsInstalled)
	if len(cs.GetVotersOutgoing()) != 0 {
		r.stats.add(StSnapshotsInstalledJoint)
	}
	if len(cs.GetLearners()) != 0 || len(cs.GetLearnersNext()) != 0 {
		r.stats.add(StSnapshotsInstalledLearners)
	}
}

// applyEntry applies one committed entry and moves the applied index to it. An entry at or below
// the applied index -- one a restarted incarnation's snapshot covers, which raft hands back when
// Config.Applied is below the snapshot's index -- is skipped.
func (r *Replica) applyEntry(e *pb.Entry) {
	r.mu.Lock()
	covered := e.GetIndex() <= r.index
	r.mu.Unlock()
	if covered {
		r.stats.add(StEntriesSkipped)
		return
	}
	switch e.GetType() {
	case pb.EntryNormal:
		r.applyOp(e.GetData())
	case pb.EntryConfChange:
		var cc pb.ConfChange
		if err := pb.UnmarshalConfChangeV1(e.GetData(), &cc); err != nil {
			panic("kvnet: a configuration change that does not decode")
		}
		r.applyConf(&cc)
	case pb.EntryConfChangeV2:
		var cc pb.ConfChangeV2
		if err := pb.UnmarshalConfChangeV2(e.GetData(), &cc); err != nil {
			panic("kvnet: a configuration change that does not decode")
		}
		r.applyConf(&cc)
	}
	r.mu.Lock()
	r.index = e.GetIndex()
	r.mu.Unlock()
}

// applyConf applies a committed configuration change to the node if it is valid on the current
// configuration (validConf), and rejects it otherwise by not applying it, as raft allows; every
// replica applies the same entries from the same configuration, so they all decide the same.
func (r *Replica) applyConf(cc pb.ConfChangeI) {
	v2 := cc.AsV2()
	r.mu.Lock()
	cur := r.cs
	r.mu.Unlock()
	if !validConf(cur, v2) {
		r.stats.add(StConfChangesRejected)
		return
	}
	cs := r.node.ApplyConfChange(cc)
	r.mu.Lock()
	r.cs = cs
	r.mu.Unlock()
	r.stats.add(StConfChangesApplied)
	if _, joint := v2.EnterJoint(); joint {
		r.stats.add(StJointEntered)
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
// they read, and returns the others. A read nobody waits for any more (timed out, or issued by
// an earlier incarnation) is dropped.
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
// timeout. If the operation was already applied here, its answer is the recorded one. Two
// clients never propose the same operation at once (the client that issued it waits for its
// answer before it retries), so at most one waits for it here.
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
	ctx, cancel := withTimeout(timeout)
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

// read reads key by a read index here, as the read of sequence number seq (the client's: never
// reused), waiting up to timeout; ok is false if no answer came.
func (r *Replica) read(seq uint64, key string, timeout time.Duration) (string, bool) {
	ch := make(chan string, 1)
	r.mu.Lock()
	if _, busy := r.reads[seq]; busy {
		// the same read sent twice (a client's retry reaching this replica again): only one waits
		r.mu.Unlock()
		return "", false
	}
	r.reads[seq] = ch
	r.mu.Unlock()
	ctx, cancel := withTimeout(timeout)
	r.node.ReadIndex(ctx, readCtx(r.id, seq, key))
	select {
	case v := <-ch:
		cancel()
		return v, true
	case <-ctx.Done():
		cancel()
	}
	r.mu.Lock()
	if r.reads[seq] == ch {
		delete(r.reads, seq)
	}
	r.mu.Unlock()
	select {
	case v := <-ch:
		return v, true
	default:
		return "", false
	}
}

// contents is a copy of the store's contents and its applied index and configuration, read at
// once.
func (r *Replica) contents() (map[string]string, uint64, *pb.ConfState) {
	r.mu.Lock()
	defer r.mu.Unlock()
	m := make(map[string]string)
	for k, v := range r.kv {
		m[k] = v
	}
	return m, r.index, r.cs
}
