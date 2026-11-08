//go:build with_tla && !goose

// (This file, the deterministic driver and the NDJSON writer, is not translated (`!goose`): it is
// not on Main's path, and it uses math/rand/v2 and encoding/json, which Perennial does not model.)
//
// Package tracecheck runs raft clusters in process and records raft's own state-machine traces
// (raft's `with_tla` build: `state_trace.go`, the events its TLA+ trace validation reads,
// `tla/Traceetcdraft.tla`), to check them against the protocol's TLA+ specification
// (`tla/etcdraft.tla`): by TLC through upstream's trace validation, and by porcupine against the
// Go transcription of the specification (package etcdraft).
//
// A cluster is driven by one goroutine: each step picks a random action (tick a node, deliver or
// drop an in-flight message, propose, propose a configuration change, restart a node, or process
// a node's Ready), so the trace's order is the order in which the events happened. The network
// delays, reorders and drops messages but never duplicates one: the specification's network is a
// multiset whose messages are each received at most once (a duplicate is not one of the trace
// specification's actions).
//
// Always off (the specification does not model them): pre-vote, check-quorum, read-index,
// leadership transfer, joint configurations. Off by default, on by Config: configuration changes
// after the bootstrap (one node added, removed or made a learner at a time), snapshots and log
// compaction, and restarts.
package tracecheck

import (
	"encoding/json"
	"fmt"
	"io"
	"math/rand/v2"
	"strconv"

	"go.etcd.io/raft/v3"
	pb "go.etcd.io/raft/v3/raftpb"
	"google.golang.org/protobuf/proto"
)

// Recorder is a raft.TraceLogger keeping every event, in the order raft reports them. The
// cluster is driven by one goroutine, so no lock is needed.
type Recorder struct {
	events []raft.TracingEvent
}

// TraceEvent records a copy of ev.
func (r *Recorder) TraceEvent(ev *raft.TracingEvent) {
	r.events = append(r.events, *ev)
}

// Events returns the recorded events.
func (r *Recorder) Events() []raft.TracingEvent {
	return r.events
}

// WriteNDJSON writes the events in the format upstream's trace validation reads
// (`tla/validate.sh`, `Traceetcdraft.tla`'s `OriginTraceLog`): one JSON object per line with
// `"tag":"trace"` and the event under `"event"`, shaped like the zap lines of raft's example
// trace, with `"ts"` the event's position (fixed width, so that validate.sh's textual sort of the
// lines keeps their order).
func WriteNDJSON(w io.Writer, events []raft.TracingEvent) error {
	for i := range events {
		ev, err := json.Marshal(&events[i])
		if err != nil {
			return err
		}
		if _, err := fmt.Fprintf(w, `{"level":"debug","ts":%d,"caller":"tracecheck","msg":"trace","tag":"trace","event":%s}`+"\n",
			1_000_000_000+i, ev); err != nil {
			return err
		}
	}
	return nil
}

// Config is a run's configuration.
type Config struct {
	Nodes     int    // the bootstrap configuration's voters, ids 1..Nodes
	Steps     int    // actions to take
	Seed      uint64 // the driver's random choices (raft's randomized election timeouts are raft's own)
	DropPct   int    // percentage of deliveries that drop the message instead
	Proposals int    // proposals to make, at most

	// ExtraNodes nodes, ids Nodes+1..Nodes+ExtraNodes, start empty (as a member being added
	// does), for configuration changes to add.
	ExtraNodes int
	// ConfChanges configuration changes to propose, at most: each adds a node of 1..Nodes+
	// ExtraNodes as a voter or a learner, or removes one.
	ConfChanges int
	// SnapshotEvery: a node takes a snapshot of its applied state and compacts its log when it
	// has applied that many entries since its last snapshot (0: never).
	SnapshotEvery int
	// Restarts nodes restarts, at most (a node restarts from its storage, as RestartNode does,
	// losing the messages it had not yet handed out). Upstream's trace specification cannot
	// match a restart: raft logs InitState in newRaft before it loads the persisted state and
	// configuration, and RestartIfLogged checks that line against the restarted state.
	Restarts int
}

// DefaultConfig is a small run: three voters, no configuration change, snapshot or restart.
func DefaultConfig(seed uint64) Config {
	return Config{Nodes: 3, Steps: 2000, Seed: seed, DropPct: 5, Proposals: 20}
}

// FullConfig is DefaultConfig with configuration changes (a fourth node, added and removed) and
// snapshots on; not restarts, which upstream's trace specification cannot match (Restarts).
func FullConfig(seed uint64) Config {
	c := DefaultConfig(seed)
	c.Steps = 3000
	c.ExtraNodes = 1
	c.ConfChanges = 4
	c.SnapshotEvery = 5
	return c
}

type node struct {
	id      uint64
	rn      *raft.RawNode
	storage *raft.MemoryStorage
	// applied is the index of the last entry the node applied; confState its configuration then
	// (what a snapshot taken now records).
	applied   uint64
	confState *pb.ConfState
	snapIndex uint64 // the index of the node's latest snapshot
}

// Sim is a cluster and its network.
type Sim struct {
	cfg      Config
	rng      *rand.Rand
	nodes    []*node
	inflight []*pb.Message
	rec      *Recorder
	proposed int

	// counts, for tests
	Delivered, Dropped, Readies, Proposed, Applied, ConfChanges, Snapshots, Restarts int
}

func (s *Sim) raftConfig(id uint64, st *raft.MemoryStorage, applied uint64) *raft.Config {
	return &raft.Config{
		ID:              id,
		ElectionTick:    10,
		HeartbeatTick:   1,
		Storage:         st,
		Applied:         applied,
		MaxSizePerMsg:   1 << 20,
		MaxInflightMsgs: 256,
		Logger:          quietLogger{},
		TraceLogger:     s.rec,
	}
}

// New starts a cluster of cfg.Nodes voters, each bootstrapped as StartNode does (RawNode.Bootstrap
// with every voter as a peer), and cfg.ExtraNodes empty nodes, all reporting to one Recorder.
func New(cfg Config) (*Sim, error) {
	s := &Sim{cfg: cfg, rng: rand.New(rand.NewPCG(cfg.Seed, 0x7261667474726163)), rec: &Recorder{}}
	var peers []raft.Peer
	for i := 1; i <= cfg.Nodes; i++ {
		peers = append(peers, raft.Peer{ID: uint64(i)})
	}
	for i := 1; i <= cfg.Nodes+cfg.ExtraNodes; i++ {
		st := raft.NewMemoryStorage()
		rn, err := raft.NewRawNode(s.raftConfig(uint64(i), st, 0))
		if err != nil {
			return nil, err
		}
		if i <= cfg.Nodes {
			if err := rn.Bootstrap(peers); err != nil {
				return nil, err
			}
		}
		s.nodes = append(s.nodes, &node{id: uint64(i), rn: rn, storage: st, confState: &pb.ConfState{}})
	}
	return s, nil
}

// Events returns the trace so far.
func (s *Sim) Events() []raft.TracingEvent { return s.rec.Events() }

func (s *Sim) node(id uint64) *node {
	if id == 0 || id > uint64(len(s.nodes)) {
		return nil
	}
	return s.nodes[id-1]
}

// Run takes cfg.Steps random actions.
func (s *Sim) Run() error {
	for i := 0; i < s.cfg.Steps; i++ {
		if err := s.step(); err != nil {
			return fmt.Errorf("step %d: %w", i, err)
		}
	}
	return nil
}

func (s *Sim) step() error {
	n := s.nodes[s.rng.IntN(len(s.nodes))]
	switch r := s.rng.IntN(100); {
	case r < 20:
		n.rn.Tick()
	case r < 58:
		s.deliver()
	case r < 63:
		if s.proposed < s.cfg.Proposals {
			s.proposed++
			s.Proposed++
			// at any node: a follower forwards it to its leader (MsgProp, not traced), a node
			// knowing no leader drops it
			_ = n.rn.Propose([]byte("v" + strconv.Itoa(s.proposed)))
		}
	case r < 64:
		if s.ConfChanges < s.cfg.ConfChanges {
			if cc := s.confChange(n); cc != nil {
				s.ConfChanges++
				_ = n.rn.ProposeConfChange(cc)
			}
		}
	case r < 65:
		if s.Restarts < s.cfg.Restarts {
			s.Restarts++
			return s.restart(n)
		}
	default:
		return s.ready(n)
	}
	return nil
}

// confChange is a configuration change for n to propose, if n is the leader, that the
// specification models (AddNewServer, AddLearner, DeleteServer of etcdraft.tla): from n's current
// configuration, a node of the cluster not a voter is added as a voter (a learner is promoted), one
// not a member is added as a learner, or a member is removed (not the last voter). The
// specification has no demotion of a voter to a learner, which raft allows (AddLearnerNode of a
// voter). Nil when n is not the leader.
func (s *Sim) confChange(n *node) *pb.ConfChange {
	st := n.rn.Status()
	if st.RaftState != raft.StateLeader || len(st.Config.Voters[1]) != 0 {
		return nil
	}
	target := uint64(1 + s.rng.IntN(len(s.nodes)))
	voters, learners := st.Config.Voters[0], st.Config.Learners
	_, isVoter := voters[target]
	_, isLearner := learners[target]
	var typ pb.ConfChangeType
	switch {
	case isVoter:
		if len(voters) == 1 {
			return nil
		}
		typ = pb.ConfChangeRemoveNode
	case isLearner:
		typ = []pb.ConfChangeType{pb.ConfChangeAddNode, pb.ConfChangeRemoveNode}[s.rng.IntN(2)]
	default:
		typ = []pb.ConfChangeType{pb.ConfChangeAddNode, pb.ConfChangeAddLearnerNode}[s.rng.IntN(2)]
	}
	return &pb.ConfChange{Type: typ.Enum(), NodeId: proto.Uint64(target)}
}

// restart replaces n's RawNode by one restarted from its storage, as RestartNode does: what n
// had not handed out in a Ready is lost. Applied is the index of n's latest snapshot, the state
// it keeps (it applies the entries after it again).
func (s *Sim) restart(n *node) error {
	rn, err := raft.NewRawNode(s.raftConfig(n.id, n.storage, n.snapIndex))
	if err != nil {
		return err
	}
	n.rn = rn
	n.applied = n.snapIndex
	if snap, err := n.storage.Snapshot(); err == nil {
		n.confState = snap.GetMetadata().GetConfState()
	}
	return nil
}

// deliver steps a random in-flight message on its target, or drops it.
func (s *Sim) deliver() {
	if len(s.inflight) == 0 {
		return
	}
	k := s.rng.IntN(len(s.inflight))
	m := s.inflight[k]
	s.inflight[k] = s.inflight[len(s.inflight)-1]
	s.inflight = s.inflight[:len(s.inflight)-1]
	dst := s.node(m.GetTo())
	src := s.node(m.GetFrom())
	if dst == nil || s.rng.IntN(100) < s.cfg.DropPct {
		s.Dropped++
		if src != nil {
			src.rn.ReportUnreachable(m.GetTo())
			if m.GetType() == pb.MsgSnap {
				src.rn.ReportSnapshot(m.GetTo(), raft.SnapshotFailure)
			}
		}
		return
	}
	s.Delivered++
	// Step may keep and write the message (raft-step-writes-caller-message): it is the
	// network's own copy, stepped once.
	_ = dst.rn.Step(m)
	if m.GetType() == pb.MsgSnap && src != nil {
		src.rn.ReportSnapshot(m.GetTo(), raft.SnapshotFinish)
	}
}

// ready handles n's Ready, if it has one: persists the snapshot, entries and hard state, sends
// the messages, applies the committed entries (configuration changes), takes a snapshot when due,
// and advances.
func (s *Sim) ready(n *node) error {
	if !n.rn.HasReady() {
		return nil
	}
	s.Readies++
	rd := n.rn.Ready()
	if !raft.IsEmptySnap(rd.Snapshot) {
		if err := n.storage.ApplySnapshot(rd.Snapshot); err != nil {
			return err
		}
		n.applied = rd.Snapshot.GetMetadata().GetIndex()
		n.snapIndex = n.applied
		n.confState = rd.Snapshot.GetMetadata().GetConfState()
	}
	if err := n.storage.Append(rd.Entries); err != nil {
		return err
	}
	if rd.HardState != nil && !raft.IsEmptyHardState(rd.HardState) {
		if err := n.storage.SetHardState(rd.HardState); err != nil {
			return err
		}
	}
	for _, m := range rd.Messages {
		s.inflight = append(s.inflight, proto.Clone(m).(*pb.Message))
	}
	confApplied := false
	for _, e := range rd.CommittedEntries {
		s.Applied++
		switch e.GetType() {
		case pb.EntryConfChange:
			cc := &pb.ConfChange{}
			if err := proto.Unmarshal(e.GetData(), cc); err != nil {
				return err
			}
			n.confState = n.rn.ApplyConfChange(cc)
			confApplied = true
		case pb.EntryConfChangeV2:
			cc := &pb.ConfChangeV2{}
			if err := proto.Unmarshal(e.GetData(), cc); err != nil {
				return err
			}
			n.confState = n.rn.ApplyConfChange(cc)
			confApplied = true
		}
		n.applied = e.GetIndex()
	}
	// A snapshot is due every SnapshotEvery entries, and right after a configuration change is
	// applied: a leader sends a follower whose next entries are compacted its storage's latest
	// snapshot, which the follower drops unless its configuration has the follower
	// (nonissues/raft-snapshot-without-recipient-livelock.md), so a member just added needs one
	// taken since (as etcd's snapshots, and examples/raft/kvreconf's Replica.run, are).
	if s.cfg.SnapshotEvery > 0 && n.applied > n.snapIndex &&
		(confApplied || n.applied >= n.snapIndex+uint64(s.cfg.SnapshotEvery)) {
		if _, err := n.storage.CreateSnapshot(n.applied, n.confState, nil); err != nil {
			return err
		}
		if err := n.storage.Compact(n.applied); err != nil {
			return err
		}
		n.snapIndex = n.applied
		s.Snapshots++
	}
	n.rn.Advance(rd)
	return nil
}

// Leaders returns the ids of the nodes that are leaders now.
func (s *Sim) Leaders() []uint64 {
	var ls []uint64
	for _, n := range s.nodes {
		if n.rn.BasicStatus().RaftState == raft.StateLeader {
			ls = append(ls, n.id)
		}
	}
	return ls
}

// MaxCommit is the largest commit index over the nodes.
func (s *Sim) MaxCommit() uint64 {
	var c uint64
	for _, n := range s.nodes {
		if hs := n.rn.BasicStatus().HardState; hs.GetCommit() > c {
			c = hs.GetCommit()
		}
	}
	return c
}
