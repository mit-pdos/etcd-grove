// Package antithesis runs a cluster of the verified raft and checks the steps its nodes take at
// raft's boundary against Antithesis's TLA+ model of etcd-io/raft (third_party/etcd-raft-formalized:
// EtcdRaft.tla, through its trace binding EtcdBinding.tla, transcribed into Go in package check).
// Main is the closed program of notes/antithesis-check-design.md (#33); its scope is the parity
// plan's (~/coordinator-notes/plans/antithesis-parity-plan.md §1-§2): every mode of Antithesis's
// simulator, drawn at random at the start of the run (DrawMode), in one program.
//
// The driver, as an executable spec of raft's client API (driver.go):
//
//   - the mode: 3 or 5 servers, all or 3 of them the initial voters, logs empty or bootstrapped
//     (BootInit's entry written to storage before start, as rawnode writes it), PreVote,
//     CheckQuorum, StepDownOnRemoval, MaxInflightMsgs, MaxSizePerMsg, AsyncStorageWrites,
//     batching, a leader sending before it writes, the write order, and which behaviours run;
//   - one goroutine per node, which owns its RawNode and MemoryStorage and takes one input at a
//     time, each one call of the client API (Step, Tick, Propose, ProposeConfChange, ReadIndex,
//     TransferLeader, Campaign, ReportSnapshot, ReportUnreachable, CreateSnapshot and Compact, a
//     storage step, a flush, a kill), followed by its Readies;
//   - one goroutine per behaviour, calling the client API on random nodes until the run stops:
//     the proposer, campaigner, reader, transferer, conf changer, snapshotter, restarter, and, by
//     mode, the flusher (batching) and the storage (AsyncStorageWrites);
//   - the network: a goroutine per message, which delivers it 0 to maxDeliveries times (lost or
//     duplicated), and reports a lost message (ReportUnreachable) and a snapshot's fate
//     (ReportSnapshot) to its sender; forwarded proposals are delivered (Mode.Forward).
//
// A node is run as Antithesis's rawnode runs it (node.go: antithesis-fm/rawnode/node.go, report
// for report): the default mode (each Ready's write announced by a `ready` and made, as one step,
// then the `send`s, `read`s and `apply`), Parallel (`mem`, the requests, `write`, `wrote`), Split
// (several `ready`s), AsyncStorageWrites (`mem`, then the queued writes and applies, each a
// storage step: `write`, `wrote`, the sends with their `cause`, `apply` with a = 1, `restore`),
// batching (`mem` per input; at a flush `flush`, `net`, `made`, the sends with b = 1, `wrote`),
// snapshots (`snap`, a leader's in `ready`/`mem`/`write` and `restore`), membership (`conf`),
// read indexes (`readreq`, `read`), restarts (`boot` from the disk; a kill drops the node's
// memory, including writes announced or queued and not made).
//
// Every report goes to one Recorder, whose lock orders them: the stream is the order in which
// they were recorded. That order is one the binding can follow (notes/antithesis-check-design.md,
// "The harness's stream"): a node's reports are recorded from its goroutine, in its program order,
// which is rawnode's; a message is recorded as sent before the network has it, so before any node
// can record its receipt; everything the binding needs at a receipt was recorded by its sender
// before the `send`; storage steps run on the node's goroutine, between two inputs, as in
// rawnode's simulator.
package antithesis

import (
	"strconv"
	"sync"

	"github.com/goose-lang/primitive"
	"go.etcd.io/raft/v3"
	pb "go.etcd.io/raft/v3/raftpb"
	"google.golang.org/protobuf/proto"

	"github.com/mit-pdos/etcd-grove/examples/raft/antithesis/check"
)

// quietLogger discards what raft logs; Fatal and Panic panic.
type quietLogger struct{}

func (quietLogger) Debug(v ...interface{})                   {}
func (quietLogger) Debugf(format string, v ...interface{})   {}
func (quietLogger) Error(v ...interface{})                   {}
func (quietLogger) Errorf(format string, v ...interface{})   {}
func (quietLogger) Info(v ...interface{})                    {}
func (quietLogger) Infof(format string, v ...interface{})    {}
func (quietLogger) Warning(v ...interface{})                 {}
func (quietLogger) Warningf(format string, v ...interface{}) {}
func (quietLogger) Fatal(v ...interface{})                   { panic("raft: fatal") }
func (quietLogger) Fatalf(format string, v ...interface{})   { panic("raft: " + format) }
func (quietLogger) Panic(v ...interface{})                   { panic("raft: panic") }
func (quietLogger) Panicf(format string, v ...interface{})   { panic("raft: " + format) }

// below is a random number in [0, n) (n > 0): primitive.RandomUint64, whose spec gives any value
// (as examples/raft/tracecheck draws its).
func below(n uint64) uint64 { return primitive.RandomUint64() % n }

// ---------------------------------------------------------------------------------------------
// The stream.

// Recorder keeps every report in the order they are recorded, from any goroutine.
type Recorder struct {
	mu     sync.Mutex
	events []*check.Event
}

func (r *Recorder) record(ev *check.Event) {
	r.mu.Lock()
	r.events = append(r.events, ev)
	r.mu.Unlock()
}

// Events is a copy of the reports recorded so far.
func (r *Recorder) Events() []*check.Event {
	r.mu.Lock()
	out := make([]*check.Event, len(r.events))
	copy(out, r.events)
	r.mu.Unlock()
	return out
}

// Name is the name reports use for node id: "raft<id>" (the binding's servers), "" for none.
func Name(id uint64) string {
	if id == 0 {
		return ""
	}
	return "raft" + strconv.FormatUint(id, 10)
}

func names(n uint64) []string {
	var out []string
	for i := uint64(1); i <= n; i++ {
		out = append(out, Name(i))
	}
	return out
}

// bootData is what the entry every log starts with holds, in a bootstrapped run (rawnode's BootData).
func bootData() []byte { return []byte("boot") }

// entryOf is rawnode's entryOf (antithesis-fm/rawnode/node.go): the bootstrapped run's first entry
// is "config"; a change of membership is "conf", its value the change it makes (changeOf); a
// normal entry is "noop" when empty and "command" (its data as the value) otherwise.
func entryOf(e *pb.Entry, n uint64) check.Entry {
	if e.GetIndex() == 1 && string(e.GetData()) == string(bootData()) {
		return check.Entry{Term: int(e.GetTerm()), Type: "config", Value: check.Value{Str: ""}}
	}
	if e.GetType() != pb.EntryType_EntryNormal {
		return check.Entry{Term: int(e.GetTerm()), Type: "conf", Value: changeOf(e, n)}
	}
	if len(e.GetData()) == 0 {
		return check.Entry{Term: int(e.GetTerm()), Type: "noop", Value: check.Value{Str: ""}}
	}
	return check.Entry{Term: int(e.GetTerm()), Type: "command", Value: check.Value{Str: string(e.GetData())}}
}

func entriesOf(es []*pb.Entry, n uint64) []check.Entry {
	out := make([]check.Entry, 0, len(es))
	for _, e := range es {
		out = append(out, entryOf(e, n))
	}
	return out
}

// confChangeOf is the change of membership entry e holds (a ConfChange or a ConfChangeV2, as raft
// decodes it), as a ConfChangeV2. The entries are raft's, made from what ProposeConfChange
// marshalled, so they decode.
func confChangeOf(e *pb.Entry) *pb.ConfChangeV2 {
	if e.GetType() == pb.EntryType_EntryConfChange {
		c1 := &pb.ConfChange{}
		if err := proto.Unmarshal(e.GetData(), c1); err != nil {
			panic("antithesis: a ConfChange entry that does not decode")
		}
		return c1.AsV2()
	}
	c := &pb.ConfChangeV2{}
	if err := proto.Unmarshal(e.GetData(), c); err != nil {
		panic("antithesis: a ConfChangeV2 entry that does not decode")
	}
	return c
}

// changeOf is rawnode's changeOf: what a change of membership does to the voters, among nodes
// 1..n: the nodes it makes voters (`add`), the nodes it makes not voters (removed, or learners:
// `remove`), each in the order of their ids (the last change of a node counts); whether it is a
// joint change; whether it leaves a joint configuration.
func changeOf(e *pb.Entry, n uint64) check.Value {
	c := confChangeOf(e)
	st := make([]uint64, n+1) // 0: not named, 1: made a voter, 2: made not a voter
	for _, ch := range c.GetChanges() {
		id := ch.GetNodeId()
		if id != 0 && id <= n && ch.GetType() != pb.ConfChangeType_ConfChangeUpdateNode {
			if ch.GetType() == pb.ConfChangeType_ConfChangeAddNode {
				st[id] = 1
			} else {
				st[id] = 2
			}
		}
	}
	add := []string{}
	remove := []string{}
	for id := uint64(1); id <= n; id++ {
		if st[id] == 1 {
			add = append(add, Name(id))
		}
		if st[id] == 2 {
			remove = append(remove, Name(id))
		}
	}
	_, joint := c.EnterJoint()
	return check.Value{IsRec: true, Add: add, Remove: remove, Joint: joint, Leave: c.LeaveJoint()}
}

// msgType is rawnode's msgTypes.
func msgType(t pb.MessageType) string {
	switch t {
	case pb.MessageType_MsgApp:
		return "app"
	case pb.MessageType_MsgAppResp:
		return "appresp"
	case pb.MessageType_MsgVote:
		return "vote"
	case pb.MessageType_MsgVoteResp:
		return "voteresp"
	case pb.MessageType_MsgHeartbeat:
		return "hb"
	case pb.MessageType_MsgHeartbeatResp:
		return "hbresp"
	case pb.MessageType_MsgPreVote:
		return "prevote"
	case pb.MessageType_MsgPreVoteResp:
		return "prevoteresp"
	case pb.MessageType_MsgSnap:
		return "snap"
	case pb.MessageType_MsgTimeoutNow:
		return "timeoutnow"
	case pb.MessageType_MsgReadIndex:
		return "readindex"
	case pb.MessageType_MsgReadIndexResp:
		return "readindexresp"
	case pb.MessageType_MsgProp:
		return "prop"
	case pb.MessageType_MsgTransferLeader:
		return "transfer"
	}
	return "other"
}

// msgOf is rawnode's msgOf, with `to` given (rawnode's `arrived` reports a message handed to a node
// as addressed to it).
func msgOf(m *pb.Message, to uint64, n uint64) check.Msg {
	index, logTerm := m.GetIndex(), m.GetLogTerm()
	if m.GetType() == pb.MessageType_MsgSnap {
		index, logTerm = m.GetSnapshot().GetMetadata().GetIndex(), m.GetSnapshot().GetMetadata().GetTerm()
	}
	return check.Msg{Has: check.MFAll, Type: msgType(m.GetType()), From: Name(m.GetFrom()), To: Name(to),
		Term: int(m.GetTerm()), Index: int(index), LogTerm: int(logTerm), Entries: entriesOf(m.GetEntries(), n),
		Commit: int(m.GetCommit()), Reject: m.GetReject(), Hint: int(m.GetRejectHint())}
}

func roleOf(s raft.StateType) string {
	if s == raft.StateLeader {
		return "leader"
	}
	if s == raft.StateCandidate {
		return "candidate"
	}
	if s == raft.StatePreCandidate {
		return "precandidate"
	}
	return "follower"
}

// ---------------------------------------------------------------------------------------------
// The storage.

// disk is a node's durable storage: what survives a restart (rawnode's MemDisk). The HardState,
// the last snapshot (nil: none) and the entries after the snapshot's index. Only the node's
// goroutine touches it, and only one goroutine of a node runs at a time (Cluster.restart).
type disk struct {
	hs   *pb.HardState
	snap *pb.Snapshot
	ents []*pb.Entry
}

func (d *disk) base() uint64 { return d.snap.GetMetadata().GetIndex() }

// save is MemDisk.Save: the HardState, if any, and the entries, which replace the log from the
// first one's index on. Raft's writes start at most one past the log's end, after the snapshot.
func (d *disk) save(hs *pb.HardState, ents []*pb.Entry) {
	if hs != nil {
		d.hs = proto.Clone(hs).(*pb.HardState)
	}
	if len(ents) > 0 {
		at := ents[0].GetIndex() - d.base() - 1
		if ents[0].GetIndex() <= d.base() || at > uint64(len(d.ents)) {
			panic("antithesis: a write that does not continue the log on disk")
		}
		var out []*pb.Entry
		out = append(out, d.ents[:at]...)
		d.ents = append(out, ents...)
	}
}

// saveSnapshot is MemDisk.SaveSnapshot: the snapshot (with the HardState, if any) replaces the
// log up to its index (restore: the whole log, a snapshot a leader sent).
func (d *disk) saveSnapshot(snap *pb.Snapshot, hs *pb.HardState, restore bool) {
	if hs != nil {
		d.hs = proto.Clone(hs).(*pb.HardState)
	}
	if restore {
		d.ents = nil
	} else {
		var out []*pb.Entry
		d.ents = append(out, d.ents[snap.GetMetadata().GetIndex()-d.base():]...)
	}
	d.snap = snap
}

// memoryOf is a MemoryStorage holding what d holds: the storage raft starts on after a restart.
func memoryOf(d *disk) *raft.MemoryStorage {
	ms := raft.NewMemoryStorage()
	if d.snap != nil {
		if err := ms.ApplySnapshot(d.snap); err != nil {
			panic("antithesis: ApplySnapshot failed on a fresh storage")
		}
	}
	if err := ms.SetHardState(d.hs); err != nil {
		panic("antithesis: SetHardState failed")
	}
	if err := ms.Append(d.ents); err != nil {
		panic("antithesis: Append failed")
	}
	return ms
}

// bootStorage is a MemoryStorage whose InitialState reports the run's initial voters as its
// ConfState while it holds no snapshot, as rawnode's store does (its `first`): every node starts
// among them, whether it is one of them or not. (A MemoryStorage reports a snapshot's ConfState,
// and takes no snapshot at index 0; raft's Bootstrap would write a configuration entry per voter,
// which neither of the binding's initial states has.)
type bootStorage struct {
	ms     *raft.MemoryStorage
	voters []uint64
}

func (s *bootStorage) InitialState() (*pb.HardState, *pb.ConfState, error) {
	hs, cs, err := s.ms.InitialState()
	if err != nil {
		return hs, cs, err
	}
	snap, err := s.ms.Snapshot()
	if err != nil {
		return hs, cs, err
	}
	if snap.GetMetadata().GetIndex() == 0 {
		return hs, &pb.ConfState{Voters: s.voters}, nil
	}
	return hs, cs, nil
}

func (s *bootStorage) Entries(lo, hi, maxSize uint64) ([]*pb.Entry, error) {
	return s.ms.Entries(lo, hi, maxSize)
}

func (s *bootStorage) Term(i uint64) (uint64, error) { return s.ms.Term(i) }

func (s *bootStorage) LastIndex() (uint64, error) { return s.ms.LastIndex() }

func (s *bootStorage) FirstIndex() (uint64, error) { return s.ms.FirstIndex() }

func (s *bootStorage) Snapshot() (*pb.Snapshot, error) { return s.ms.Snapshot() }
