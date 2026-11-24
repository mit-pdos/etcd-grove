// Package antithesis runs a cluster of the verified raft and checks the steps its nodes take at
// raft's boundary against Antithesis's TLA+ model of etcd-io/raft (third_party/etcd-raft-formalized:
// EtcdRaft.tla, through its trace binding EtcdBinding.tla, transcribed into Go in package check).
// Main is the closed program of notes/antithesis-check-design.md (#33).
//
// The harness: each node is a raft.RawNode on a MemoryStorage, owned by one goroutine that takes
// one input at a time (a message, a tick, a proposal) and then takes raft's Readies until there
// is none, each in Antithesis's default mode (antithesis-fm/rawnode/node.go, `drain`): the write
// (HardState and entries) announced by a `ready` report and made, as one step; the messages, each
// reported (`send`) before it is handed to the network; the committed entries reported (`apply`)
// and applied; Advance. The network delivers each message from a goroutine of its own after a
// random delay (so messages are reordered), or drops it; a proposer hands proposals to random
// nodes (a follower drops them: forwarding is off, notes/antithesis-s4-design.md §7); an isolator cuts a random node off the network
// for a while, which makes the others elect another leader.
//
// Every report goes to one Recorder, whose lock orders them: the stream is the order in which
// they were recorded. That order is one the binding can follow (notes/antithesis-check-design.md,
// "The harness's stream"):
//
//   - a node's reports are recorded from its goroutine, one at a time, so in its program order,
//     which is rawnode's: the reports of one input, `recv` first (recorded just before the first
//     report the message causes, rawnode's reportCause), then per Ready `ready`, `send`s, `apply`;
//   - a message is recorded as sent before the network has it (send hands it over after the
//     report), so before any node can record its receipt; everything the binding needs at a
//     receipt was recorded by its sender before the `send` (the leader log and commits of a
//     request: the sender's earlier `ready`s; a vote request's fact: the candidate's `ready` that
//     wrote its term), and everything a later step needs from the receiver's answer (a grant, an
//     ack) is recorded by the receiver's `send` or `ready` before the answer reaches the network;
//   - nothing else connects two nodes: a proposal is an input of one node, and the isolator only
//     drops messages.
//
// Scope (#33's decisions, notes/antithesis-check-design.md §8): three voters with empty logs
// (EtcdBindingEmpty.cfg: each storage reports the voters as its ConfState and holds no entry),
// synchronous storage, PreVote and CheckQuorum off, proposal forwarding off (notes/antithesis-s4-design.md
// §7), no restarts,
// snapshots, membership changes or read indexes.
package antithesis

import (
	"strconv"
	"sync"
	"time"

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

// entryOf is rawnode's entryOf (antithesis-fm/rawnode/node.go): a normal entry is "noop" when
// empty and "command" (its data as the value) otherwise. A change of membership is out of scope:
// nothing proposes one, and raft makes none by itself in a configuration that is not joint.
func entryOf(e *pb.Entry) check.Entry {
	if e.GetType() != pb.EntryType_EntryNormal {
		panic("antithesis: a membership change (out of scope)")
	}
	if len(e.GetData()) == 0 {
		return check.Entry{Term: int(e.GetTerm()), Type: "noop", Value: check.Value{Str: ""}}
	}
	return check.Entry{Term: int(e.GetTerm()), Type: "command", Value: check.Value{Str: string(e.GetData())}}
}

func entriesOf(es []*pb.Entry) []check.Entry {
	out := make([]check.Entry, 0, len(es))
	for _, e := range es {
		out = append(out, entryOf(e))
	}
	return out
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
func msgOf(m *pb.Message, to uint64) check.Msg {
	index, logTerm := m.GetIndex(), m.GetLogTerm()
	if m.GetType() == pb.MessageType_MsgSnap {
		index, logTerm = m.GetSnapshot().GetMetadata().GetIndex(), m.GetSnapshot().GetMetadata().GetTerm()
	}
	return check.Msg{Has: check.MFAll, Type: msgType(m.GetType()), From: Name(m.GetFrom()), To: Name(to),
		Term: int(m.GetTerm()), Index: int(index), LogTerm: int(logTerm), Entries: entriesOf(m.GetEntries()),
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

// bootStorage is a MemoryStorage whose InitialState reports the cluster's voters as its
// ConfState while it holds no snapshot: a node starts with an empty log, at term 0, among the
// voters (EtcdBindingEmpty.cfg), as rawnode's storage does with BOOT=0. (A MemoryStorage reports a
// snapshot's ConfState, and takes no snapshot at index 0; raft's Bootstrap would write a
// configuration entry per voter, which the binding's initial state does not have.)
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

// ---------------------------------------------------------------------------------------------
// The cluster.

// Config is a run's configuration.
type Config struct {
	Nodes      uint64        // voters, ids 1..Nodes
	Proposals  uint64        // proposals, one after another at random nodes
	ProposeGap time.Duration // the pause between two proposals
	Settle     time.Duration // how long the cluster runs after the last proposal
	Tick       time.Duration // the nodes' tick interval
	MaxDelay   time.Duration // a message's delay is uniform in [0, MaxDelay]
	DropPct    uint64        // percentage of messages dropped
	// Isolations: the isolator cuts a random node off the network (every message from or to it
	// dropped) for IsolateFor, that many times, one after another.
	Isolations uint64
	IsolateFor time.Duration
}

// DefaultConfig is Main's run: three voters, 60 proposals, three isolations (leader changes).
func DefaultConfig() Config {
	return Config{Nodes: 3, Proposals: 60, ProposeGap: 5 * time.Millisecond, Settle: 100 * time.Millisecond,
		Tick: 2 * time.Millisecond, MaxDelay: 4 * time.Millisecond, DropPct: 5, Isolations: 3,
		IsolateFor: 80 * time.Millisecond}
}

// input kinds.
const (
	inMsg uint64 = iota
	inProp
)

// input is one input to a node: a message (handed to RawNode.Step) or a proposal.
type input struct {
	kind uint64
	msg  *pb.Message
	data []byte
}

// node is one raft node. Everything but in is its goroutine's own.
type node struct {
	id      uint64
	name    string
	rn      *raft.RawNode
	storage *raft.MemoryStorage
	in      chan input

	role               string
	term, vote, commit uint64     // the HardState on disk
	cause              *check.Msg // the report of the message being handled, not recorded yet
	applied            uint64
}

// Cluster is a run.
type Cluster struct {
	cfg   Config
	rec   *Recorder
	nodes []*node
	stop  chan struct{}

	isoMu    sync.Mutex
	isolated uint64 // the node cut off the network now (0: none)

	nodesWg sync.WaitGroup // the nodes' goroutines
	netWg   sync.WaitGroup // the network's goroutines
}

func (c *Cluster) node(id uint64) *node {
	if id == 0 || id > uint64(len(c.nodes)) {
		return nil
	}
	return c.nodes[id-1]
}

func (c *Cluster) isolatedNow() uint64 {
	c.isoMu.Lock()
	x := c.isolated
	c.isoMu.Unlock()
	return x
}

func (c *Cluster) isolate(id uint64) {
	c.isoMu.Lock()
	c.isolated = id
	c.isoMu.Unlock()
}

// Events is the stream.
func (c *Cluster) Events() []*check.Event { return c.rec.Events() }

// Servers is the binding's Server (and InitVoters): the nodes' names.
func (c *Cluster) Servers() check.Set { return check.SetOf(names(c.cfg.Nodes)) }

// RunCluster runs a cluster: it starts the nodes and their goroutines, makes the proposals and
// isolations, lets the cluster settle, stops it, and returns it (its stream is Events).
func RunCluster(cfg Config) *Cluster {
	c := &Cluster{cfg: cfg, rec: &Recorder{}, stop: make(chan struct{})}
	var voters []uint64
	for i := uint64(1); i <= cfg.Nodes; i++ {
		voters = append(voters, i)
	}
	for i := uint64(1); i <= cfg.Nodes; i++ {
		ms := raft.NewMemoryStorage()
		rc := &raft.Config{
			ID:              i,
			ElectionTick:    10,
			HeartbeatTick:   1,
			Storage:         &bootStorage{ms: ms, voters: voters},
			MaxSizePerMsg:   1 << 20,
			MaxInflightMsgs: 256,
			// Forwarding disabled because raft.Step's spec covers only local MsgProp (From 0 or the
			// node itself): a follower drops a proposal instead of forwarding it. Re-enable with option
			// (a) of notes/antithesis-s4-design.md §7 (widen raft.Step/RawNode.Step to a network MsgProp): #44.
			DisableProposalForwarding: true,
			Logger:                    quietLogger{},
		}
		rn, err := raft.NewRawNode(rc)
		if err != nil {
			panic("antithesis: NewRawNode failed")
		}
		n := &node{id: i, name: Name(i), rn: rn, storage: ms, in: make(chan input, 1024), role: "follower"}
		c.nodes = append(c.nodes, n)
	}
	for _, n := range c.nodes {
		// rawnode's Start: what the node recovered (nothing), then raft's first Readies.
		c.rec.record(&check.Event{E: "boot", Node: n.name,
			Has: check.FTerm | check.FVote | check.FCommit | check.FLastIndex | check.FLastTerm | check.FApplied |
				check.FVoters | check.FOutgoing,
			Vote: "", Voters: names(cfg.Nodes), Outgoing: []string{}})
		c.drain(n, "boot")
	}
	for _, n := range c.nodes {
		c.nodesWg.Add(1)
		go c.run(n)
	}

	var drivers sync.WaitGroup
	drivers.Add(2)
	go func() { // the isolator
		for k := uint64(0); k < cfg.Isolations; k++ {
			time.Sleep(cfg.IsolateFor / 2)
			c.isolate(1 + below(cfg.Nodes))
			time.Sleep(cfg.IsolateFor)
			c.isolate(0)
		}
		drivers.Done()
	}()
	go func() { // the proposer
		for k := uint64(1); k <= cfg.Proposals; k++ {
			n := c.nodes[below(cfg.Nodes)]
			c.deliver(n, input{kind: inProp, data: []byte("v" + strconv.FormatUint(k, 10))})
			time.Sleep(cfg.ProposeGap)
		}
		drivers.Done()
	}()
	drivers.Wait()
	time.Sleep(cfg.Settle)

	close(c.stop)
	c.nodesWg.Wait()
	c.netWg.Wait()
	return c
}

// deliver hands inp to n, unless the run stops first.
func (c *Cluster) deliver(n *node, inp input) {
	select {
	case n.in <- inp:
	case <-c.stop:
	}
}

// run is node n's goroutine: one input at a time, each followed by its Readies.
func (c *Cluster) run(n *node) {
	ticker := time.NewTicker(c.cfg.Tick)
	for {
		select {
		case <-c.stop:
			ticker.Stop()
			c.nodesWg.Done()
			return
		case <-ticker.C:
			n.rn.Tick()
			c.drain(n, "tick")
		case inp := <-n.in:
			if inp.kind == inMsg {
				// rawnode's Step: the message is reported (`recv`) before the first report it
				// causes, if any. Its report is made before Step, which takes the message over.
				cause := msgOf(inp.msg, n.id)
				n.cause = &cause
				_ = n.rn.Step(inp.msg)
				c.drain(n, "recv")
				n.cause = nil
			} else {
				_ = n.rn.Propose(inp.data)
				c.drain(n, "propose")
			}
		}
	}
}

// reportCause is rawnode's: the message being handled is reported once, before the first report
// that follows from it.
func (c *Cluster) reportCause(n *node) {
	if n.cause != nil {
		c.rec.record(&check.Event{E: "recv", Node: n.name, Has: check.FMsg, Msg: *n.cause})
		n.cause = nil
	}
}

// drain is rawnode's drain in its default mode: for each Ready, the write (announced, then made),
// the messages, the committed entries, Advance.
func (c *Cluster) drain(n *node, by string) {
	for n.rn.HasReady() {
		rd := n.rn.Ready()
		role := n.role
		if rd.SoftState != nil {
			role = roleOf(rd.SoftState.RaftState)
		}
		term, vote, commit := n.term, n.vote, n.commit
		hsNew := rd.HardState != nil && !raft.IsEmptyHardState(rd.HardState)
		if hsNew {
			term, vote, commit = rd.HardState.GetTerm(), rd.HardState.GetVote(), rd.HardState.GetCommit()
		}
		if !raft.IsEmptySnap(rd.Snapshot) {
			panic("antithesis: a snapshot (out of scope)")
		}
		write := hsNew || len(rd.Entries) > 0
		if write || role != n.role {
			c.reportCause(n)
			var first uint64
			if len(rd.Entries) > 0 {
				first = rd.Entries[0].GetIndex()
			}
			c.rec.record(&check.Event{E: "ready", Node: n.name,
				Has: check.FBy | check.FRole | check.FTerm | check.FVote | check.FCommit | check.FFirst | check.FEntries,
				By:  by, Role: role, Term: int(term), Vote: Name(vote), Commit: int(commit), First: int(first),
				Entries: entriesOf(rd.Entries)})
			if write {
				// One atomic write: the storage is the node's goroutine's alone.
				if err := n.storage.Append(rd.Entries); err != nil {
					panic("antithesis: Append failed")
				}
				if hsNew {
					if err := n.storage.SetHardState(rd.HardState); err != nil {
						panic("antithesis: SetHardState failed")
					}
				}
				n.term, n.vote, n.commit = term, vote, commit
			}
			n.role = role
		}
		for _, m := range rd.Messages {
			c.reportCause(n)
			c.rec.record(&check.Event{E: "send", Node: n.name, Has: check.FBy | check.FMsg, By: by,
				Msg: msgOf(m, m.GetTo())})
			c.send(proto.Clone(m).(*pb.Message))
		}
		if len(rd.CommittedEntries) > 0 {
			c.reportCause(n)
			c.rec.record(&check.Event{E: "apply", Node: n.name, Has: check.FBy | check.FFirst | check.FEntries,
				By: by, First: int(rd.CommittedEntries[0].GetIndex()), Entries: entriesOf(rd.CommittedEntries)})
			n.applied = rd.CommittedEntries[len(rd.CommittedEntries)-1].GetIndex()
		}
		n.rn.Advance(rd)
	}
}

// send delivers m after a random delay, or drops it, from a goroutine of its own.
func (c *Cluster) send(m *pb.Message) {
	delay := time.Duration(below(uint64(c.cfg.MaxDelay) + 1))
	drop := below(100) < c.cfg.DropPct
	c.netWg.Add(1)
	go func() {
		time.Sleep(delay)
		iso := c.isolatedNow()
		if iso != 0 && (iso == m.GetTo() || iso == m.GetFrom()) {
			drop = true
		}
		dst := c.node(m.GetTo())
		if dst != nil && !drop {
			c.deliver(dst, input{kind: inMsg, msg: m})
		}
		c.netWg.Done()
	}()
}
