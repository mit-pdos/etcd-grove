//go:build with_tla

// Package tracecheck runs raft clusters in process and records raft's own state-machine traces
// (raft's `with_tla` build: `state_trace.go`, the events its TLA+ trace validation reads,
// `tla/Traceetcdraft.tla`), to check them against the protocol's TLA+ specification
// (`tla/etcdraft.tla`): by TLC through upstream's trace validation, and by porcupine against a Go
// transcription of the specification.
//
// A cluster is driven by one goroutine: each step picks a random action (tick a node, deliver or
// drop an in-flight message, propose, or process a node's Ready), so the trace's order is the
// order in which the events happened. The network delays, reorders and drops messages but never
// duplicates one: the specification's network is a multiset whose messages are each received at
// most once (a duplicate is not one of the trace specification's actions).
//
// What is turned off, for now (the specification does not model it, or a first harness does not
// need it): pre-vote, check-quorum, log compaction and snapshots, read-index, leadership
// transfer, and configuration changes after the bootstrap.
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
}

// DefaultConfig is a small run.
func DefaultConfig(seed uint64) Config {
	return Config{Nodes: 3, Steps: 2000, Seed: seed, DropPct: 5, Proposals: 20}
}

type node struct {
	id      uint64
	rn      *raft.RawNode
	storage *raft.MemoryStorage
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
	Delivered, Dropped, Readies, Proposed, Applied int
}

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
func (quietLogger) Fatal(v ...interface{})                   { panic(fmt.Sprint(v...)) }
func (quietLogger) Fatalf(format string, v ...interface{})   { panic(fmt.Sprintf(format, v...)) }
func (quietLogger) Panic(v ...interface{})                   { panic(fmt.Sprint(v...)) }
func (quietLogger) Panicf(format string, v ...interface{})   { panic(fmt.Sprintf(format, v...)) }

// New starts a cluster of cfg.Nodes voters, each bootstrapped as StartNode does (RawNode.Bootstrap
// with every voter as a peer), all reporting to one Recorder.
func New(cfg Config) (*Sim, error) {
	s := &Sim{cfg: cfg, rng: rand.New(rand.NewPCG(cfg.Seed, 0x7261667474726163)), rec: &Recorder{}}
	var peers []raft.Peer
	for i := 1; i <= cfg.Nodes; i++ {
		peers = append(peers, raft.Peer{ID: uint64(i)})
	}
	for i := 1; i <= cfg.Nodes; i++ {
		st := raft.NewMemoryStorage()
		rn, err := raft.NewRawNode(&raft.Config{
			ID:              uint64(i),
			ElectionTick:    10,
			HeartbeatTick:   1,
			Storage:         st,
			MaxSizePerMsg:   1 << 20,
			MaxInflightMsgs: 256,
			Logger:          quietLogger{},
			TraceLogger:     s.rec,
		})
		if err != nil {
			return nil, err
		}
		if err := rn.Bootstrap(peers); err != nil {
			return nil, err
		}
		s.nodes = append(s.nodes, &node{id: uint64(i), rn: rn, storage: st})
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
	case r < 60:
		s.deliver()
	case r < 65:
		if s.proposed < s.cfg.Proposals {
			s.proposed++
			s.Proposed++
			// at any node: a follower forwards it to its leader (MsgProp, not traced), a node
			// knowing no leader drops it
			_ = n.rn.Propose([]byte("v" + strconv.Itoa(s.proposed)))
		}
	default:
		return s.ready(n)
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
	if dst == nil || s.rng.IntN(100) < s.cfg.DropPct {
		s.Dropped++
		if src := s.node(m.GetFrom()); src != nil {
			src.rn.ReportUnreachable(m.GetTo())
		}
		return
	}
	s.Delivered++
	// Step may keep and write the message (raft-step-writes-caller-message): it is the
	// network's own copy, stepped once.
	_ = dst.rn.Step(m)
}

// ready handles n's Ready, if it has one: persists the snapshot, entries and hard state, sends
// the messages, applies the committed configuration changes, and advances.
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
	for _, e := range rd.CommittedEntries {
		s.Applied++
		switch e.GetType() {
		case pb.EntryConfChange:
			cc := &pb.ConfChange{}
			if err := proto.Unmarshal(e.GetData(), cc); err != nil {
				return err
			}
			n.rn.ApplyConfChange(cc)
		case pb.EntryConfChangeV2:
			cc := &pb.ConfChangeV2{}
			if err := proto.Unmarshal(e.GetData(), cc); err != nil {
				return err
			}
			n.rn.ApplyConfChange(cc)
		}
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
