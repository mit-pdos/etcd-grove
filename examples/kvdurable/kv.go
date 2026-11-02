// Package kvdurable is kvreconf's replicated key-value store on raft -- snapshots, configuration
// changes, a lossy network, leadership disruptions, reads by read index, every choice the
// application may make made at random -- made durable: a replica keeps its raft storage in a file
// of the durable package, and replicas crash and restart from their files. Like kvreconf, its test
// program is meant to be read as a specification of how an application may use raft, now
// including what raft asks of a durable application, and the freedom it leaves it:
//
//   - A replica's durable state is its raft storage, the hard state, the latest snapshot (which
//     holds the store's replicated state) and the log, written whole to one file (Storage.encode)
//     in one atomic durable.Write. The replica keeps its own image of those contents, changed
//     with the storage by each of its storage changes, and writes the image, never reading the
//     storage back: raft owns the uncommitted log between Readys, and the storage's Snapshot does
//     not say which snapshot it returns. Every write is of the contents at a moment between two
//     of the replica's groups of storage changes (Replica.dmu), so that the file always holds
//     contents the storage had.
//   - What raft requires is written before it is relied on: a Ready's snapshot, entries and a
//     hard state that changes the term or the vote (raft.MustSync) are written before the Ready's
//     messages are sent -- except at a replica whose last reported role is leader, which may send
//     them first, at random (as etcd's leader does, the Raft thesis's 10.2.1) -- and always before
//     the Ready's committed entries are applied and before Advance.
//   - What raft does not require may be written late or not at all, at random: a hard state that
//     changes only the commit index (etcd does not sync it), a snapshot taken, a compaction.
//   - A crash (Cluster.Crash, at random times, of a random replica: a member, a removed one or a
//     newcomer, a leader or not) stops the replica's every goroutine and its node, and writes
//     nothing more; the replica restarts at once from its file (raft.RestartNode on the stored
//     storage, with the stored snapshot as its replicated state and Config.Applied chosen at
//     random among the indices raft allows at or below the snapshot's, or left 0). Entries raft
//     then hands back that the snapshot already covers are skipped. A replica with no file (a
//     crash before its first write) restarts empty, as it started.
//
// What it leaves out: the clients do not crash (the operation ids are the cluster's, in memory),
// and a crash keeps the files whole (durable.Write is atomic; the file's replacement is the
// durable package's, not this one's).
//
// Every Put and Get goes through the raft log; Read is a linearizable read by a read index
// (Node.ReadIndex). An operation is identified by an id the cluster gives it, so that a client
// may retry it at another replica, or after the replica crashed, without its taking effect twice.
package kvdurable

import (
	"context"
	"encoding/binary"
	"sync"
	"time"

	"github.com/goose-lang/primitive"
	"github.com/mit-pdos/etcd-grove/examples/durable"
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

// maxSeq is the last operation id and read sequence number: a cluster that has used up its
// operation ids (Cluster.do), or its read sequence numbers (readSeqs), stops issuing them, so
// that an id is never reused (a reused one would be answered with another operation's answer).
// 2^64 - 1 of them: it does not happen.
const maxSeq = ^uint64(0)

// readSeqs issues the sequence numbers of the reads (Replica.read), one counter for the cluster's
// every replica and incarnation: a read's context outlives its incarnation (a read index response
// to a crashed incarnation's read may reach the next incarnation), so a number reused by the next
// incarnation would answer its read with the old read's index and key.
type readSeqs struct {
	mu   sync.Mutex
	last uint64
}

// next is a fresh sequence number; ok is false once they are used up (maxSeq).
func (s *readSeqs) next() (uint64, bool) {
	s.mu.Lock()
	defer s.mu.Unlock()
	if s.last == maxSeq {
		return 0, false
	}
	s.last++
	return s.last, true
}

// Replica is one incarnation of a replica of the store: its id, its durable file, its raft node
// and storage, and, under mu, its replicated state as of its applied index -- the store's
// contents, the operations applied (by their encoding, each with its answer: the key's value after
// it) and the configuration -- and the operations and reads waiting for their answers here. An
// incarnation ends when it crashes (crash) or the cluster stops (stop); the replica's next
// incarnation (Cluster.restart) starts from the file.
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
	// groups. crashed, under it, is set by the crash: once it is, nothing writes the
	// file, so the next incarnation reads what this one last wrote.
	dmu     sync.Mutex
	crashed bool

	mu      sync.Mutex
	kv      map[string]string
	applied map[string]string
	cs      *pb.ConfState
	index   uint64
	waiters map[string]chan string
	seqs    *readSeqs
	reads   map[uint64]chan string
}

// newReplica is an incarnation of replica id on node, a node just started on storage, whose
// durable file is file, at the replicated state (kv, applied, cs) of index (its storage's
// snapshot's: 0 and the bootstrap configuration if it has none), raft's applied index at start
// rafted (Config.Applied, or the log's start if that is 0), ticked every tick; seqs issues its
// reads' sequence numbers; send delivers the node's messages. It starts the incarnation's loop,
// its node's clock and its snapshot goroutine.
func newReplica(id uint64, file string, node raft.Node, storage *Storage, kv map[string]string, applied map[string]string,
	cs *pb.ConfState, index uint64, rafted uint64, tick time.Duration, stats *Stats, seqs *readSeqs,
	send func([]*pb.Message)) *Replica {
	hs := storage.img.hs
	r := &Replica{id: id, file: file, node: node, storage: storage, stats: stats, tick: tick, stopc: make(chan struct{}),
		snapc:   make(chan snapReq, 1),
		runDone: make(chan struct{}, 1), tickDone: make(chan struct{}, 1), snapDone: make(chan struct{}, 1),
		cs: proto.Clone(cs).(*pb.ConfState), index: index,
		kv: kv, applied: applied, seqs: seqs,
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

// stop stops the incarnation for good: its loop, its clock, its snapshot goroutine and its node.
// It stops the node only once the loop and the clock have returned, so that the loop never meets
// a stopped node: every call it makes (the Ready, ApplyConfChange, Advance) is on a running one.
// (Other goroutines -- proposers, readers, the network's Step -- may still call a stopped node;
// they handle its answers.)
func (r *Replica) stop() {
	close(r.stopc)
	<-r.runDone
	<-r.tickDone
	<-r.snapDone
	r.node.Stop()
}

// crash crashes the incarnation: from now on it writes nothing to its file, and it stops (stop).
// What it does between the two is what it might have done before the crash, but for the writes:
// it sends no message that needs a write it can no longer make (run). The last critical section of
// dmu, after stop, does nothing at run time: once run and the snapshot goroutine have returned, it
// lets the proof take the file's writer out of dmu's invariant.
func (r *Replica) crash() {
	r.dmu.Lock()
	r.crashed = true
	r.dmu.Unlock()
	r.stop()
	r.dmu.Lock()
	r.dmu.Unlock()
}

// persist writes the storage's image to the file; false if the incarnation has crashed, which
// then writes nothing.
func (r *Replica) persist() bool {
	r.dmu.Lock()
	ok := !r.crashed
	if ok {
		durable.Write(r.file, string(r.storage.encode()))
		r.stats.add(&r.stats.FileWrites)
	}
	r.dmu.Unlock()
	return ok
}

// run handles the node's Readys, in the order raft documents: install the snapshot, if any (in
// the storage and its image, then as the replicated state: install); save the hard state and
// append the entries (in both); write the image to the file if raft needs it durable, and send
// the messages; note the read states; apply the committed entries in order (a configuration change to the node,
// Node.ApplyConfChange, before the Advance that acknowledges it); answer the reads whose index is
// applied; Advance. A Ready whose entries would take the log past maxIndex stops the loop (it does
// not happen). snapIndex is the index of the latest snapshot asked for (the stored one's, at
// start), hs the storage's hard state (its image's), rafted raft's applied index (the last entry it handed back,
// or snapshot it installed, before the last Advance: after a restart below the snapshot, below the
// replicated state's index).
//
// Durability: a Ready that installs a snapshot, appends entries or changes the term or the vote
// (raft.MustSync) is written before its messages are sent, and before it is applied and
// Advanced; one that changes only the commit index is written one time in two (raft does not
// need it durable: a restarted node learns the commit index again from the leader); one that
// changes nothing is not written. A replica whose last reported role is leader (the Readys'
// SoftState) may send the messages before the write (one time in two), as etcd does: its own
// acknowledgement of the entries is stepped only at Advance, after the write. If the incarnation
// has crashed, the write fails and the loop stops before sending what needed it.
//
// Snapshots and compaction are the application's to choose, and done in a goroutine of their own
// (snapshotter), as etcd's apply thread takes its snapshots beside the raft goroutine that appends
// and installs them: after any entry it applies and after any Advance, the loop may ask for a
// snapshot of its replicated state, and after any Advance for a compaction up to its applied
// index as raft knows it (the bound MemoryStorage.Compact documents: what it applied before the
// last Advance; after a restart, raft may still be handing back entries below the replicated
// state's index), without waiting (request).
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
				panic("kvdurable: a snapshot whose data does not decode")
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
				r.stats.add(&r.stats.CommitUnwritten)
			}
		}
		first := lead && sync && oneIn(2)
		if first {
			r.stats.add(&r.stats.LeaderSentFirst)
			send(rd.Messages)
		}
		if write && !r.persist() {
			// crashed: the Ready's messages, if not sent yet, needed the write
			r.runDone <- struct{}{}
			return
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

// request asks the snapshot goroutine, without waiting, for a snapshot of the replicated state at
// the applied index if snap (unless the latest one asked for is already that recent, or no
// configuration is applied yet: a new replica's, before it catches up), and for a
// compaction up to the least of the applied index and bound, unless bound is 0 (run passes raft's
// applied index, after an Advance); a request is dropped if the goroutine has one pending. It
// returns the index of the latest snapshot asked for.
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

// snapshot does what req asks: it takes the snapshot (in the storage and its image), which may be
// out of date (ErrSnapOutOfDate: the storage holds one at least as recent, which run installed),
// as etcd's apply thread allows; and it compacts the log (in both) to a random index from its
// first one to the least of the requested bound and the stored snapshot's index as known
// (compacting past the stored snapshot, the leader would have no snapshot to send a follower that
// needs the compacted entries: nonissues/raft-compact-past-snapshot.md), if there is one. Neither
// needs to be durable: it writes the image to the file afterwards one time in two (a later write,
// of a Ready, writes it anyway). It returns what is known of the stored snapshot's index after it.
func (r *Replica) snapshot(req snapReq, known uint64) uint64 {
	changed := false
	if req.data != nil {
		r.dmu.Lock()
		err := r.storage.CreateSnapshot(req.index, req.cs, req.data)
		r.dmu.Unlock()
		if err == nil {
			changed = true
			r.stats.add(&r.stats.SnapshotsTaken)
			if len(req.cs.GetVotersOutgoing()) != 0 {
				r.stats.add(&r.stats.SnapshotsTakenJoint)
			}
		} else if err != raft.ErrSnapOutOfDate {
			panic("kvdurable: CreateSnapshot: " + err.Error())
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
				r.stats.add(&r.stats.Compactions)
			}
		}
	}
	if changed && oneIn(2) {
		r.persist()
	}
	return known
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

// applyEntry applies one committed entry and moves the applied index to it. An entry at or below
// the applied index -- one a restarted incarnation's snapshot covers, which raft hands back when
// Config.Applied is below the snapshot's index -- is skipped.
func (r *Replica) applyEntry(e *pb.Entry) {
	r.mu.Lock()
	covered := e.GetIndex() <= r.index
	r.mu.Unlock()
	if covered {
		r.stats.add(&r.stats.EntriesSkipped)
		return
	}
	switch e.GetType() {
	case pb.EntryNormal:
		r.applyOp(e.GetData())
	case pb.EntryConfChange:
		var cc pb.ConfChange
		if err := proto.Unmarshal(e.GetData(), &cc); err != nil {
			panic("kvdurable: a configuration change that does not decode")
		}
		r.applyConf(&cc)
	case pb.EntryConfChangeV2:
		var cc pb.ConfChangeV2
		if err := proto.Unmarshal(e.GetData(), &cc); err != nil {
			panic("kvdurable: a configuration change that does not decode")
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
// the read sequence numbers are used up: readSeqs).
func (r *Replica) read(key string, timeout time.Duration) (string, bool) {
	ch := make(chan string, 1)
	seq, ok := r.seqs.next()
	if !ok {
		return "", false
	}
	r.mu.Lock()
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
