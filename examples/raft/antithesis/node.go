package antithesis

import (
	"sync/atomic"

	"go.etcd.io/raft/v3"
	pb "go.etcd.io/raft/v3/raftpb"
	"google.golang.org/protobuf/proto"

	"github.com/mit-pdos/etcd-grove/examples/raft/antithesis/check"
)

// The node: one RawNode, run as Antithesis's rawnode runs it (antithesis-fm/rawnode/node.go, at
// the commit third_party/etcd-raft-formalized's README names), report for report. Each method
// below is the rawnode method of the same name; their comments say where they differ. Everything
// here runs on the node's goroutine.

// node is one raft node: its durable disk, and its memory (everything else), which a kill drops.
type node struct {
	c    *Cluster
	id   uint64
	name string
	in   chan input
	disk *disk

	rn    *raft.RawNode
	store *raft.MemoryStorage // raft's Storage: what raft knows is on disk
	role  string
	hs    *pb.HardState // the HardState on disk, as raft knows it
	// cause is the report of the message being handled (made before RawNode.Step, which takes the
	// message over), until it is recorded (reportCause).
	cause *check.Msg
	// applied: the index of the last entry handed to the state machine, or of the snapshot it was
	// last replaced by.
	applied uint64
	// conf is the configuration raft counts with (for the conf changer).
	conf *pb.ConfState

	// Batch: the `mem` reports with w = 1 since the last Ready.
	items int
	// Async, Batch: the HardState raft has in memory; the same as of the last Ready.
	mhs, rhs *pb.HardState
	// Async: the queued writes (oldest first) and whether one is taken and not done; the same for
	// the batches of entries to apply; the queued writes that replace the log by a snapshot a
	// leader sent; the write made and the batch applied whose Done steps are still to come.
	writes    []*writeJob
	inflight  bool
	applies   []*applyJob
	applying  bool
	restoring int
	wip       *writeJob
	aip       *applyJob

	// The configurations raft was switched to since the snapshot in store, oldest first.
	confs []confAt
	// Batch: how many times raft, leading, appended the entry that leaves a joint configuration.
	// Accessed only atomically (sync/atomic): the logger, which raft calls from inside its own
	// calls, adds to it.
	autoLeft uint64
	// The index of the last snapshot a leader sent that raft was handed.
	confBase uint64

	// A kill: fuse > 0 is the number of reports until the node dies (rawnode's simulator's fuse);
	// dead: it has died, and nothing it does from here on is recorded, written or sent; its Ready
	// loops and storage steps stop at once (its raft is dropped with it, `run`).
	fuse uint64
	dead bool
}

// confAt is the configuration the change at an index made.
type confAt struct {
	index uint64
	cs    *pb.ConfState
}

// writeJob is rawnode's Write: what one Ready asked to be written, and the messages that wait for it.
type writeJob struct {
	hs     *pb.HardState // nil: none
	snap   *pb.Snapshot  // nil: none; otherwise the log is replaced by it
	ents   []*pb.Entry
	after  *pb.HardState // the HardState on disk after it
	resp   []*pb.Message
	cause  *check.Msg // the message the Ready answered
	by     string
	writes bool // there is something to write
	k      int  // Batch: how many `mem` reports the write is of; -1 otherwise
}

// applyJob is rawnode's Apply: the committed entries one Ready handed over, or a snapshot.
type applyJob struct {
	ents    []*pb.Entry
	restore *pb.Snapshot
	resp    []*pb.Message
	by      string
}

// nodeLogger discards what raft logs, as quietLogger, and counts (for a batching node) raft's
// automatic leaving of a joint configuration, which raft shows nowhere else before the Ready
// (rawnode's autoLeave).
type nodeLogger struct {
	quietLogger
	n *node
}

func (l *nodeLogger) Infof(format string, v ...interface{}) {
	if format == "initiating automatic transition out of joint configuration %s" {
		atomic.AddUint64(&l.n.autoLeft, 1)
	}
}

func u64p(x uint64) *uint64 { return &x }

func b2i(b bool) int {
	if b {
		return 1
	}
	return 0
}

func firstIndex(ents []*pb.Entry) uint64 {
	if len(ents) == 0 {
		return 0
	}
	return ents[0].GetIndex()
}

// ---------------------------------------------------------------------------------------------
// Reports, writes and sends: everything a node does that others can see.

// emit records ev, unless the node is dead or dies now (its fuse burns down before a report).
func (n *node) emit(ev *check.Event) bool {
	if n.dead {
		return false
	}
	if n.fuse > 0 {
		n.fuse--
		if n.fuse == 0 {
			n.dead = true
			return false
		}
	}
	ev.Node = n.name
	n.c.rec.record(ev)
	return true
}

// announce records a write's announcement (`ready`, `write`, `net`); a kill due at the next
// report may also land between it and the write.
func (n *node) announce(ev *check.Event) bool {
	if !n.emit(ev) {
		return false
	}
	if n.fuse == 1 && below(2) == 0 {
		n.fuse = 0
		n.dead = true
		return false
	}
	return true
}

func (n *node) saveDisk(hs *pb.HardState, ents []*pb.Entry) {
	if !n.dead {
		n.disk.save(hs, ents)
	}
}

func (n *node) saveSnapshotDisk(snap *pb.Snapshot, hs *pb.HardState, restore bool) {
	if !n.dead {
		n.disk.saveSnapshot(snap, hs, restore)
	}
}

// sendMsg hands m to the network (Config.Send).
func (n *node) sendMsg(m *pb.Message) {
	if !n.dead {
		n.c.send(proto.Clone(m).(*pb.Message))
	}
}

func (n *node) entries(es []*pb.Entry) []check.Entry { return entriesOf(es, n.c.mode.Nodes) }

func (n *node) msg(m *pb.Message) check.Msg { return msgOf(m, m.GetTo(), n.c.mode.Nodes) }

// stateEv is a report of kind e with rawnode's `state` fields: what raft has in memory, or what is
// on disk after a write.
func (n *node) stateEv(e string, hs *pb.HardState, ents []*pb.Entry) *check.Event {
	return &check.Event{E: e, Has: check.FTerm | check.FVote | check.FCommit | check.FFirst | check.FEntries,
		Term: int(hs.GetTerm()), Vote: Name(hs.GetVote()), Commit: int(hs.GetCommit()),
		First: int(firstIndex(ents)), Entries: n.entries(ents)}
}

func withByRole(ev *check.Event, by, role string) *check.Event {
	ev.Has = ev.Has | check.FBy | check.FRole
	ev.By = by
	ev.Role = role
	return ev
}

func snapRef(s *pb.Snapshot) check.SnapRef {
	return check.SnapRef{Index: int(s.GetMetadata().GetIndex()), Term: int(s.GetMetadata().GetTerm())}
}

func withSnap(ev *check.Event, s *pb.Snapshot) *check.Event {
	ev.Has = ev.Has | check.FSnap
	ev.Snap = snapRef(s)
	return ev
}

func (n *node) sendEv(by string, m *pb.Message) *check.Event {
	return &check.Event{E: "send", Has: check.FBy | check.FMsg, By: by, Msg: n.msg(m)}
}

func (n *node) batchSendEv(by string, m *pb.Message) *check.Event {
	ev := n.sendEv(by, m)
	ev.Has = ev.Has | check.FB
	return ev
}

func (n *node) causeSendEv(by string, m *pb.Message, cause *check.Msg) *check.Event {
	ev := n.sendEv(by, m)
	ev.Has = ev.Has | check.FCause
	ev.Cause = []check.Msg{}
	if cause != nil {
		ev.Cause = []check.Msg{*cause}
	}
	return ev
}

func (n *node) confEv(e string, index uint64, cs *pb.ConfState) *check.Event {
	return &check.Event{E: e, Has: check.FIndex | check.FVoters | check.FOutgoing, Index: int(index),
		Voters: idNames(cs.GetVoters()), Outgoing: idNames(cs.GetVotersOutgoing())}
}

func idNames(ids []uint64) []string {
	out := make([]string, 0, len(ids))
	for _, id := range ids {
		out = append(out, Name(id))
	}
	return out
}

// reportCause records the message being handled, once, before the first report that follows
// from it.
func (n *node) reportCause() {
	if n.cause != nil {
		m := *n.cause
		n.cause = nil
		n.emit(&check.Event{E: "recv", Has: check.FMsg, Msg: m})
	}
}

// ---------------------------------------------------------------------------------------------
// raft's Storage.

func (n *node) storeSave(hs *pb.HardState, ents []*pb.Entry) {
	if hs != nil {
		if err := n.store.SetHardState(hs); err != nil {
			panic("antithesis: SetHardState failed")
		}
	}
	if len(ents) > 0 {
		if err := n.store.Append(ents); err != nil {
			panic("antithesis: Append failed")
		}
	}
}

func (n *node) storeRestore(snap *pb.Snapshot) {
	if err := n.store.ApplySnapshot(snap); err != nil {
		panic("antithesis: ApplySnapshot of a leader's snapshot failed")
	}
}

// storeConf is the configuration of the snapshot in store, or the initial voters.
func (n *node) storeConf() *pb.ConfState {
	snap, err := n.store.Snapshot()
	if err != nil || snap.GetMetadata().GetIndex() == 0 {
		return &pb.ConfState{Voters: n.c.initVoters}
	}
	return snap.GetMetadata().GetConfState()
}

func (n *node) storeBase() uint64 {
	snap, err := n.store.Snapshot()
	if err != nil {
		return 0
	}
	return snap.GetMetadata().GetIndex()
}

// ---------------------------------------------------------------------------------------------
// Start (a node's boot, and its restart).

// start is rawnode's Start: it reports what is on the disk (`boot`) and starts raft on it. A
// bootstrapped run's node first writes the entry every node's log starts with, unreported.
func (n *node) start() {
	m := n.c.mode
	d := n.disk
	if m.Boot && len(d.ents) == 0 && d.snap == nil && raft.IsEmptyHardState(d.hs) {
		d.save(&pb.HardState{Term: u64p(1)}, []*pb.Entry{{Term: u64p(1), Index: u64p(1), Data: bootData()}})
	}
	n.dead, n.fuse = false, 0
	n.store = memoryOf(d)
	hs := copyHardState(d.hs)
	n.hs, n.mhs, n.rhs = hs, hs, hs
	n.role = "follower"
	n.cause = nil
	n.items = 0
	n.writes, n.inflight, n.applies, n.applying, n.restoring = nil, false, nil, false, 0
	n.wip, n.aip = nil, nil
	n.confs, n.confBase = nil, 0
	atomic.StoreUint64(&n.autoLeft, 0)
	n.applied = n.storeBase()
	cs := n.storeConf()
	n.conf = cs
	last, _ := n.store.LastIndex()
	lastTerm, _ := n.store.Term(last)
	n.emit(&check.Event{E: "boot",
		Has: check.FTerm | check.FVote | check.FCommit | check.FLastIndex | check.FLastTerm | check.FApplied |
			check.FVoters | check.FOutgoing,
		Term: int(hs.GetTerm()), Vote: Name(hs.GetVote()), Commit: int(hs.GetCommit()), LastIdx: int(last),
		LastTerm: int(lastTerm), Applied: int(n.applied), Voters: idNames(cs.GetVoters()),
		Outgoing: idNames(cs.GetVotersOutgoing())})
	rn, err := raft.NewRawNode(&raft.Config{
		ID:              n.id,
		ElectionTick:    electionTick,
		HeartbeatTick:   heartbeatTick,
		Storage:         &bootStorage{ms: n.store, voters: n.c.initVoters},
		MaxSizePerMsg:   m.MaxSizePerMsg,
		MaxInflightMsgs: int(m.MaxInflightMsgs),
		// Set, as rawnode sets it: raft takes MaxSizePerMsg for it otherwise, and with
		// MaxSizePerMsg 0 then panics at its first apply (their patches/README.md, E2).
		MaxCommittedSizePerReady: maxCommittedSizePerReady,
		PreVote:                  m.PreVote,
		CheckQuorum:              m.CheckQuorum,
		StepDownOnRemoval:        m.StepDownOnRemoval,
		AsyncStorageWrites:       m.Async,
		Logger:                   &nodeLogger{n: n},
	})
	if err != nil {
		panic("antithesis: NewRawNode failed")
	}
	n.rn = rn
	// A restarted node is handed its committed entries again here: the state machine starts empty.
	n.drain("boot")
	n.alone()
}

// ---------------------------------------------------------------------------------------------
// Inputs: each is one call of the client API, then its Readies (or, batching, its `mem`).

// step hands raft a message from another node.
func (n *node) step(m *pb.Message) {
	batch := n.c.mode.Batch
	snap := m.GetType() == pb.MessageType_MsgSnap
	if batch && snap {
		n.flush() // a snapshot from a leader is handled alone
	}
	prop := m.GetType() == pb.MessageType_MsgProp // read before Step, which may keep m (a forward)
	cause := msgOf(m, n.id, n.c.mode.Nodes)
	n.cause = &cause
	err := n.rn.Step(m)
	if batch && snap {
		n.drain("recv")
		n.alone()
		n.cause = nil
		return
	}
	var ents []*pb.Entry
	if err == nil && prop {
		ents = m.GetEntries()
	}
	n.input("recv", ents)
	n.cause = nil
}

// input follows an input: the Readies, or (batching) the report of what raft has in memory.
func (n *node) input(by string, ents []*pb.Entry) {
	if !n.c.mode.Batch {
		n.drain(by)
		return
	}
	n.note(by, ents)
}

// alone follows a Ready a batching node took as one that does not batch.
func (n *node) alone() {
	if !n.c.mode.Batch {
		return
	}
	if !n.c.mode.Async {
		n.mhs = n.hs
	}
	n.note("write", nil)
}

// note reports, in a batching node, what raft has in memory after an input (`mem`), if the input
// changed it or was a request to append. ents is what the input asked a leader to append, if raft
// did not refuse.
func (n *node) note(by string, ents []*pb.Entry) {
	st := n.rn.BasicStatus()
	hs := n.mhs
	if st.HardState.GetTerm() != hs.GetTerm() || st.HardState.GetVote() != hs.GetVote() ||
		st.HardState.GetCommit() != hs.GetCommit() {
		hs = &pb.HardState{Term: u64p(st.HardState.GetTerm()), Vote: u64p(st.HardState.GetVote()),
			Commit: u64p(st.HardState.GetCommit())}
	}
	role := roleOf(st.SoftState.RaftState)
	term := st.HardState.GetTerm()
	// What a leader appended: the empty entry its term starts with, or what it was asked to and
	// did not refuse, and the entry that leaves a joint configuration, if raft appended it.
	var app []*pb.Entry
	left := atomic.SwapUint64(&n.autoLeft, 0)
	if role == "leader" {
		if n.role != "leader" {
			app = []*pb.Entry{{Term: u64p(term)}}
		} else {
			for _, e := range ents {
				app = append(app, &pb.Entry{Term: u64p(term), Type: e.Type, Data: e.GetData()})
			}
			for ; left > 0; left-- {
				app = append(app, &pb.Entry{Term: u64p(term), Type: pb.EntryConfChangeV2.Enum()})
			}
		}
	}
	request := n.cause != nil && n.cause.Type == "app" && n.cause.Term == int(term)
	if hs == n.mhs && role == n.role && !request && len(app) == 0 {
		return
	}
	w := 0
	if hs != n.mhs || request || len(app) > 0 {
		w = 1
	}
	ev := &check.Event{E: "mem", Has: check.FBy | check.FRole | check.FW | check.FTerm | check.FVote | check.FCommit,
		By: by, Role: role, W: w, Term: int(hs.GetTerm()), Vote: Name(hs.GetVote()), Commit: int(hs.GetCommit())}
	if role == "leader" {
		ev.Has = ev.Has | check.FEntries
		ev.Entries = n.entries(app)
	}
	n.reportCause()
	n.emit(ev)
	n.role = role
	n.mhs = hs
	n.items += w
}

// flushes reports that the oldest k `mem` reports not yet written are part of the next write.
func (n *node) flushes(k int) {
	for j := 0; j < k; j++ {
		n.emit(&check.Event{E: "flush", Has: check.FMore, More: b2i(j > 0)})
	}
}

// flush takes raft's Ready in a batching node: everything that followed from the inputs since the
// last one.
func (n *node) flush() {
	if !n.c.mode.Batch {
		return
	}
	if n.c.mode.Async {
		n.drainAsync("batch")
		if n.items > 0 {
			// Reports of something to write, and raft asked for no write.
			n.writes = append(n.writes, &writeJob{after: n.rhs, by: "batch", k: n.items})
			n.items = 0
		}
		return
	}
	for !n.dead && n.rn.HasReady() {
		rd := n.rn.Ready()
		if !raft.IsEmptySnap(rd.Snapshot) {
			// A leader's snapshot is stepped alone (step), and nothing else makes a Ready hold one.
			panic("antithesis: a snapshot in a batch")
		}
		hs := n.hs
		if !raft.IsEmptyHardState(rd.HardState) {
			hs = rd.HardState
		}
		write := hs != n.hs || len(rd.Entries) > 0
		k := n.items
		n.items = 0
		n.flushes(k)
		if write {
			var whs *pb.HardState
			if hs != n.hs {
				whs = hs
			}
			n.announce(n.stateEv("net", hs, rd.Entries))
			n.saveDisk(whs, rd.Entries)
			n.storeSave(whs, rd.Entries)
			n.hs = hs
		} else if k > 0 {
			n.emit(n.stateEv("net", hs, nil))
		}
		if k > 0 || write {
			n.emit(&check.Event{E: "made"})
		}
		if n.dead {
			return // died before its write: nothing more it does is seen; raft is dropped with it
		}
		for _, m := range rd.Messages {
			n.emit(n.batchSendEv("batch", m))
			n.sendMsg(m)
		}
		if k > 0 || write {
			n.emit(&check.Event{E: "wrote"})
		}
		n.reads(rd)
		n.applyCommitted("batch", rd.CommittedEntries)
		n.rn.Advance(rd)
		for _, m := range rd.Messages {
			n.sent(m)
		}
		// Raft takes note of its own write here: a leader's commit index can move.
		n.note("write", nil)
	}
	if n.items > 0 {
		k := n.items
		n.items = 0
		n.flushes(k)
		n.emit(n.stateEv("net", n.hs, nil))
		n.emit(&check.Event{E: "made"})
		n.emit(&check.Event{E: "wrote"})
	}
}

// applyCommitted hands committed entries to the state machine (`apply`), telling raft of each
// change of membership among them.
func (n *node) applyCommitted(by string, ents []*pb.Entry) {
	if len(ents) == 0 {
		return
	}
	n.reportCause()
	n.emit(&check.Event{E: "apply", Has: check.FBy | check.FFirst | check.FEntries, By: by,
		First: int(ents[0].GetIndex()), Entries: n.entries(ents)})
	for _, e := range ents {
		n.switchConf(e)
	}
	n.applied = ents[len(ents)-1].GetIndex()
}

func (n *node) tick() {
	n.rn.Tick()
	n.input("tick", nil)
}

func (n *node) campaign() {
	_ = n.rn.Campaign()
	n.input("campaign", nil)
}

// propose: an error means raft did not append it; a follower passes it on to its leader.
func (n *node) propose(data []byte) {
	err := n.rn.Propose(data)
	var ents []*pb.Entry
	if err == nil {
		ents = []*pb.Entry{{Data: data}}
	}
	n.input("propose", ents)
}

// proposeConfChange asks raft to append a change of membership. A batching node does what
// RawNode.ProposeConfChange does (marshal, then Step a local proposal) with the message kept, as
// rawnode does: raft puts the entry it appends instead, if it refuses the change, in the message.
func (n *node) proposeConfChange(cc pb.ConfChangeI) {
	if !n.c.mode.Batch {
		_ = n.rn.ProposeConfChange(cc)
		n.input("propose", nil)
		return
	}
	typ, data, err := pb.MarshalConfChange(cc)
	if err != nil {
		return
	}
	m := &pb.Message{Type: pb.MessageType_MsgProp.Enum(), From: u64p(n.id),
		Entries: []*pb.Entry{{Type: typ.Enum(), Data: data}}}
	err = n.rn.Step(m)
	var ents []*pb.Entry
	if err == nil {
		ents = m.GetEntries()
	}
	n.input("propose", ents)
}

// switchConf tells raft that a change of membership is applied, if e is one, and reports the
// configuration raft counts with from here on (`conf`).
func (n *node) switchConf(e *pb.Entry) {
	if e.GetType() == pb.EntryType_EntryNormal {
		return
	}
	if e.GetIndex() <= n.confBase {
		// Raft has since been handed a snapshot that stands for this entry, and has its
		// configuration (their patches/README.md, N7).
		return
	}
	var cc pb.ConfChangeI
	if e.GetType() == pb.EntryType_EntryConfChange {
		c1 := &pb.ConfChange{}
		if err := proto.Unmarshal(e.GetData(), c1); err != nil {
			panic("antithesis: a ConfChange entry that does not decode")
		}
		cc = c1
	} else {
		cc = confChangeOf(e)
	}
	cs := n.rn.ApplyConfChange(cc)
	n.confs = append(n.confs, confAt{index: e.GetIndex(), cs: cs})
	n.conf = cs
	n.emit(n.confEv("conf", e.GetIndex(), cs))
}

// confState is the configuration as of an index the node has applied.
func (n *node) confState(index uint64) *pb.ConfState {
	cs := n.storeConf()
	for _, c := range n.confs {
		if c.index <= index {
			cs = c.cs
		}
	}
	return cs
}

// readIndex asks raft for a read index (`readreq`); raft's answer is a ReadState of a later Ready
// (`read`, reads).
func (n *node) readIndex(ctx string) {
	n.emit(&check.Event{E: "readreq", Has: check.FCtx, Ctx: ctx})
	n.rn.ReadIndex([]byte(ctx))
	n.input("read", nil)
}

func (n *node) reads(rd raft.Ready) {
	for _, rs := range rd.ReadStates {
		n.reportCause()
		n.emit(&check.Event{E: "read", Has: check.FCtx | check.FIndex, Ctx: string(rs.RequestCtx),
			Index: int(rs.Index)})
	}
}

// unreachable tells raft that a message to a peer was not delivered.
func (n *node) unreachable(id uint64) {
	n.rn.ReportUnreachable(id)
	n.input("tick", nil)
}

func (n *node) transferLeader(to uint64) {
	n.rn.TransferLeader(to)
	n.input("transfer", nil)
}

// snapshotStatus tells raft whether a snapshot it sent to `to` was delivered.
func (n *node) snapshotStatus(to uint64, ok bool) {
	st := raft.SnapshotFinish
	if !ok {
		st = raft.SnapshotFailure
	}
	n.rn.ReportSnapshot(to, st)
	n.input("snapstatus", nil)
}

// snapshot puts a snapshot of the state machine, as of index, in place of the log up to there
// (`snap`), if it may: index past the snapshot in store, applied, within the commit index on disk
// (raft does not start on a snapshot beyond it), nothing being applied, and no leader's snapshot
// waiting to be written (it could reach the disk after this one).
func (n *node) snapshot(index uint64) {
	if index <= n.storeBase() || index > n.applied || index > n.hs.GetCommit() || n.applying || n.restoring > 0 {
		return
	}
	term, err := n.store.Term(index)
	if err != nil {
		return
	}
	cs := n.confState(index)
	snap := &pb.Snapshot{Metadata: &pb.SnapshotMetadata{Index: u64p(index), Term: u64p(term), ConfState: cs}}
	n.emit(&check.Event{E: "snap", Has: check.FIndex | check.FTerm, Index: int(index), Term: int(term)})
	n.saveSnapshotDisk(snap, nil, false)
	if _, err := n.store.CreateSnapshot(index, cs, nil); err != nil {
		return
	}
	if err := n.store.Compact(index); err != nil {
		return
	}
	k := 0
	for k < len(n.confs) && n.confs[k].index <= index {
		k++
	}
	n.confs = n.confs[k:]
}

// sent follows every message handed to the network: unless the program reports how snapshots
// fare (Mode.SnapStatus), raft is told at once that a snapshot it sent arrived.
func (n *node) sent(m *pb.Message) {
	if m.GetType() == pb.MessageType_MsgSnap && !n.c.mode.SnapStatus {
		n.rn.ReportSnapshot(m.GetTo(), raft.SnapshotFinish)
	}
}

// ---------------------------------------------------------------------------------------------
// The Readies.

// drain takes raft's Readies until there is none. By default, per Ready: the write (announced,
// then made, as one step, or in Mode.Split's parts), the messages, the read states, the committed
// entries, Advance. A leader's snapshot replaces the log (one write) and then the state machine.
func (n *node) drain(by string) {
	if n.c.mode.Async {
		n.drainAsync(by)
		return
	}
	for n.rn.HasReady() {
		rd := n.rn.Ready()
		role := n.role
		if rd.SoftState != nil {
			role = roleOf(rd.SoftState.RaftState)
		}
		hs := n.hs
		if !raft.IsEmptyHardState(rd.HardState) {
			hs = rd.HardState
		}
		write := hs != n.hs || len(rd.Entries) > 0
		early := n.c.mode.Parallel && role == "leader"
		if !raft.IsEmptySnap(rd.Snapshot) {
			if len(rd.Entries) > 0 {
				panic("antithesis: a Ready with a snapshot and entries")
			}
			n.reportCause()
			var whs *pb.HardState
			if hs != n.hs {
				whs = hs
			}
			n.announce(withSnap(withByRole(n.stateEv("ready", hs, nil), by, role), rd.Snapshot))
			n.saveSnapshotDisk(rd.Snapshot, whs, true)
			n.storeRestore(rd.Snapshot)
			n.confBase = rd.Snapshot.GetMetadata().GetIndex()
			n.confs = nil
			n.conf = rd.Snapshot.GetMetadata().GetConfState()
			n.storeSave(whs, nil)
			n.hs = hs
			n.role = role
			n.restored(rd.Snapshot, false)
			n.applied = rd.Snapshot.GetMetadata().GetIndex()
		} else if early {
			n.parallel(by, role, hs, rd)
		} else if write || role != n.role {
			n.reportCause()
			if write {
				for _, p := range n.parts(hs, rd.Entries) {
					n.announce(withByRole(n.stateEv("ready", p.after, p.ents), by, role))
					n.saveDisk(p.hs, p.ents)
					n.storeSave(p.hs, p.ents)
					n.hs = p.after
				}
			} else {
				n.emit(withByRole(n.stateEv("ready", hs, nil), by, role))
			}
			n.role = role
		}
		for _, m := range rd.Messages {
			if early && isRequest(m) {
				continue // sent already
			}
			n.reportCause()
			n.emit(n.sendEv(by, m))
			n.sendMsg(m)
		}
		n.reads(rd)
		n.applyCommitted(by, rd.CommittedEntries)
		n.rn.Advance(rd)
		for _, m := range rd.Messages {
			n.sent(m)
		}
	}
}

// restored replaces the state machine by a snapshot (`restore`; later: with Async, a = 1).
func (n *node) restored(snap *pb.Snapshot, later bool) {
	ev := n.confEv("restore", snap.GetMetadata().GetIndex(), snap.GetMetadata().GetConfState())
	if later {
		ev.Has = ev.Has | check.FA
	}
	n.emit(ev)
}

func isRequest(m *pb.Message) bool {
	return m.GetType() == pb.MessageType_MsgApp || m.GetType() == pb.MessageType_MsgHeartbeat
}

// parallel is a leader's Ready with Mode.Parallel, up to its write: the report of what raft did
// (`mem`), the requests to append and heartbeats, and then the write (`write`, `wrote`).
func (n *node) parallel(by, role string, hs *pb.HardState, rd raft.Ready) {
	write := hs != n.hs || len(rd.Entries) > 0
	if write || role != n.role {
		n.reportCause()
		ev := withByRole(n.stateEv("mem", hs, rd.Entries), by, role)
		ev.Has = ev.Has | check.FW
		ev.W = b2i(write)
		n.emit(ev)
	}
	n.role = role
	for _, m := range rd.Messages {
		if isRequest(m) {
			n.reportCause()
			n.emit(n.sendEv(by, m))
			n.sendMsg(m)
		}
	}
	if write {
		var whs *pb.HardState
		if hs != n.hs {
			whs = hs
		}
		n.announce(n.stateEv("write", hs, rd.Entries))
		n.saveDisk(whs, rd.Entries)
		n.emit(&check.Event{E: "wrote"})
		n.storeSave(whs, rd.Entries)
		n.hs = hs
	}
}

// part is one write: a HardState (nil for none) and entries, and the HardState on disk after it.
type part struct {
	hs    *pb.HardState
	ents  []*pb.Entry
	after *pb.HardState
}

// parts is the writes a Ready's state is made in: one, or several in Mode.Split's order.
func (n *node) parts(hs *pb.HardState, ents []*pb.Entry) []part {
	changed := hs != n.hs
	var w *pb.HardState
	if changed {
		w = hs
	}
	var out []part
	split := n.c.mode.Split
	if split == splitTermEntriesCommit {
		// The term and the vote with the old commit index, then the entries, then the commit index.
		cur := n.hs
		if hs.GetTerm() != cur.GetTerm() || hs.GetVote() != cur.GetVote() {
			tv := &pb.HardState{Term: hs.Term, Vote: hs.Vote, Commit: u64p(cur.GetCommit())}
			out = append(out, part{hs: tv, ents: nil, after: tv})
			cur = tv
		}
		if len(ents) > 0 {
			out = append(out, part{hs: nil, ents: ents, after: cur})
		}
		if hs.GetCommit() != cur.GetCommit() {
			out = append(out, part{hs: hs, ents: nil, after: hs})
		}
		return out
	}
	if split == splitHardStateEntries {
		if changed {
			out = append(out, part{hs: hs, ents: nil, after: hs})
		}
		if len(ents) > 0 {
			out = append(out, part{hs: nil, ents: ents, after: hs})
		}
		return out
	}
	if split == splitEntriesHardState {
		if len(ents) > 0 {
			out = append(out, part{hs: nil, ents: ents, after: n.hs})
		}
		if changed {
			out = append(out, part{hs: hs, ents: nil, after: hs})
		}
		return out
	}
	return append(out, part{hs: w, ents: ents, after: hs})
}

// drainAsync takes raft's Readies with AsyncStorageWrites: it reports what raft did in memory
// (`mem`), queues the write and the entries to apply, and sends what does not wait.
//
// A request for votes (MsgVote) waits for the write of its Ready: rawnode's rule (its default,
// Config.NoHoldVote off), because raft sends it at once with AsyncStorageWrites, before the
// candidate's new term and last entries are on disk, and that is not safe (their
// patches/README.md, E1, etcd-io/raft#551: raft.go's send holds only MsgAppResp, MsgVoteResp and
// MsgPreVoteResp until written, in our fork as upstream). A pre-vote request is sent at once, as
// rawnode sends it: it changes no term and asks for nothing durable. Config.NoHoldVote (tests
// only: TestE1Reproducer, E1=1) turns the hold off.
func (n *node) drainAsync(by string) {
	batch := n.c.mode.Batch && by == "batch"
	for !n.dead && n.rn.HasReady() {
		rd := n.rn.Ready()
		var snap *pb.Snapshot
		if !raft.IsEmptySnap(rd.Snapshot) {
			if len(rd.Entries) > 0 {
				panic("antithesis: a Ready with a snapshot and entries")
			}
			snap = rd.Snapshot
			n.confBase = snap.GetMetadata().GetIndex()
			n.conf = snap.GetMetadata().GetConfState()
		}
		role := n.role
		if rd.SoftState != nil {
			role = roleOf(rd.SoftState.RaftState)
		}
		hs := n.rhs
		if !raft.IsEmptyHardState(rd.HardState) {
			hs = rd.HardState
		}
		var app, apl *pb.Message
		var out []*pb.Message
		for _, m := range rd.Messages {
			if m.GetTo() == raft.LocalAppendThread {
				app = m
			} else if m.GetTo() == raft.LocalApplyThread {
				apl = m
			} else {
				out = append(out, m)
			}
		}
		cause := n.cause
		write := hs != n.rhs || len(rd.Entries) > 0 || snap != nil
		if write && app == nil {
			panic("antithesis: raft changed its state and asked for no write")
		}
		if batch && snap != nil {
			panic("antithesis: a snapshot in a batch")
		}
		if !batch && (write || role != n.role) {
			ev := withByRole(n.stateEv("mem", hs, rd.Entries), by, role)
			ev.Has = ev.Has | check.FW
			ev.W = b2i(write)
			if snap != nil {
				withSnap(ev, snap)
			}
			n.reportCause()
			n.emit(ev)
		}
		if !batch {
			n.role = role
		}
		var job *writeJob
		if app != nil {
			job = &writeJob{ents: rd.Entries, snap: snap, after: hs, resp: app.GetResponses(), cause: cause, by: by,
				writes: write, k: -1}
			if batch {
				job.k = n.items
				n.items = 0
			}
			if snap != nil {
				n.restoring++
			}
			if hs != n.rhs {
				job.hs = hs
			}
			n.writes = append(n.writes, job)
		}
		n.rhs = hs
		if !batch {
			n.mhs = hs
		}
		for _, m := range out {
			if !n.c.cfg.NoHoldVote && m.GetType() == pb.MessageType_MsgVote && job != nil {
				job.resp = append(job.resp, m)
				continue
			}
			if batch {
				n.emit(n.batchSendEv(by, m))
			} else {
				n.reportCause()
				n.emit(n.causeSendEv(by, m, cause))
			}
			n.sendMsg(m)
			n.sent(m)
		}
		n.reads(rd)
		if apl != nil {
			n.applies = append(n.applies, &applyJob{ents: apl.GetEntries(), resp: apl.GetResponses(), by: by})
		}
	}
}

// runWrite announces the oldest queued write and makes it (rawnode's NextWrite and RunWrite).
func (n *node) runWrite(w *writeJob) {
	if w.k >= 0 {
		n.flushes(w.k)
		if w.writes {
			n.announce(n.stateEv("net", w.after, w.ents))
			n.saveDisk(w.hs, w.ents)
		} else if w.k > 0 {
			n.emit(n.stateEv("net", w.after, nil))
		}
		if w.k > 0 || w.writes {
			n.emit(&check.Event{E: "made"})
		}
		return
	}
	if !w.writes {
		return
	}
	ev := n.stateEv("write", w.after, w.ents)
	if w.snap != nil {
		n.announce(withSnap(ev, w.snap))
		n.saveSnapshotDisk(w.snap, w.hs, true)
	} else {
		n.announce(ev)
		n.saveDisk(w.hs, w.ents)
	}
	n.emit(&check.Event{E: "wrote"})
}

// doneWrite sends the messages that waited for the write and tells raft it is made.
func (n *node) doneWrite(w *writeJob) {
	n.inflight = false
	if n.dead {
		return
	}
	if w.writes {
		if w.snap != nil {
			// The state machine is replaced after what it was handed before, and before what
			// raft hands it next.
			n.restoring--
			n.storeRestore(w.snap)
			n.confs = nil
			n.applies = append(n.applies, &applyJob{restore: w.snap, by: w.by})
		}
		n.storeSave(w.hs, w.ents)
		n.hs = w.after
	}
	for _, m := range w.resp {
		if m.GetTo() == n.id {
			continue
		}
		if w.k >= 0 {
			n.emit(n.batchSendEv(w.by, m))
		} else {
			n.emit(n.causeSendEv(w.by, m, w.cause))
		}
		n.sendMsg(m)
	}
	if w.k > 0 || (w.k == 0 && w.writes) {
		n.emit(&check.Event{E: "wrote"})
	}
	for _, m := range w.resp {
		if m.GetTo() == n.id {
			_ = n.rn.Step(m)
		}
	}
	if n.c.mode.Batch {
		n.note("write", nil)
		return
	}
	n.drainAsync("write")
}

// runApply hands the entries to the state machine (`apply` with a = 1), or replaces it by a
// leader's snapshot (`restore`).
func (n *node) runApply(a *applyJob) {
	if a.restore != nil {
		n.restored(a.restore, true)
		return
	}
	if len(a.ents) == 0 {
		return
	}
	n.emit(&check.Event{E: "apply", Has: check.FBy | check.FFirst | check.FEntries | check.FA, By: a.by,
		First: int(a.ents[0].GetIndex()), Entries: n.entries(a.ents)})
}

// doneApply tells raft the entries are applied, after telling it of each change of membership
// among them.
func (n *node) doneApply(a *applyJob) {
	n.applying = false
	if n.dead {
		return
	}
	if a.restore != nil {
		n.applied = a.restore.GetMetadata().GetIndex()
	} else if len(a.ents) > 0 {
		n.applied = a.ents[len(a.ents)-1].GetIndex()
		for _, e := range a.ents {
			n.switchConf(e)
		}
	}
	for _, m := range a.resp {
		_ = n.rn.Step(m)
	}
	if n.c.mode.Batch {
		n.note("apply", nil)
		return
	}
	n.drainAsync("apply")
}

// work is one step of the node's queued storage work with AsyncStorageWrites, any of those that
// can come next (rawnode's simulator's `work`): the next write is made; the messages that waited
// for the made one leave; the next committed entries are applied; raft is told they are.
func (n *node) work() {
	var jobs []uint64
	if n.wip != nil {
		jobs = append(jobs, jobDoneWrite)
	} else if len(n.writes) > 0 && !n.inflight {
		jobs = append(jobs, jobRunWrite)
	}
	if n.aip != nil {
		jobs = append(jobs, jobDoneApply)
	} else if len(n.applies) > 0 && !n.applying {
		jobs = append(jobs, jobRunApply)
	}
	if len(jobs) == 0 {
		return
	}
	j := jobs[below(uint64(len(jobs)))]
	if j == jobRunWrite {
		w := n.writes[0]
		n.writes = n.writes[1:]
		n.inflight = true
		n.runWrite(w)
		n.wip = w
	} else if j == jobDoneWrite {
		w := n.wip
		n.wip = nil
		n.doneWrite(w)
	} else if j == jobRunApply {
		a := n.applies[0]
		n.applies = n.applies[1:]
		n.applying = true
		n.runApply(a)
		n.aip = a
	} else {
		a := n.aip
		n.aip = nil
		n.doneApply(a)
	}
}

// The storage jobs.
const (
	jobRunWrite uint64 = iota
	jobDoneWrite
	jobRunApply
	jobDoneApply
)
