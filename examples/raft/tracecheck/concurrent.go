//go:build with_tla || goose

package tracecheck

import (
	"context"
	"fmt"
	"strconv"

	"github.com/goose-lang/primitive"
	"sync"
	"sync/atomic"
	"time"

	"go.etcd.io/raft/v3"
	pb "go.etcd.io/raft/v3/raftpb"
	"google.golang.org/protobuf/proto"
)

// The concurrent harness: each replica is a raft.Node (node.go's run goroutine) with an
// application goroutine that ticks it, handles its Readies (persists, sends, applies, snapshots)
// and advances it; the network delivers each message from a goroutine of its own, after a random
// delay (so messages are reordered), through Node.Step, or drops it; a proposer and a proposer of
// configuration changes run concurrently. Every replica reports to one SyncRecorder, whose lock
// orders the events: the trace is the order in which they were logged.
//
// That order is one the trace specification can step through: a replica's events are logged from
// its run goroutine, one at a time, so in its program order; and a message is logged as sent (in
// raft's send, on the sender's run goroutine) before the Ready that hands it out, and the
// application sends it only after Advance, which the run loop takes after logging that Ready
// (acceptReady): so the Ready is logged before the network has the message, so before its receipt.
// (Sending before Advance, as etcd does, lets a receipt be logged before the sender's Ready line,
// which the trace specification cannot follow: notes/trace-validation-sim.md, round 1's F1.)

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

// below is a random number in [0, n) (n > 0), as the other harnesses draw theirs
// (examples/raft/kvreconf): primitive.RandomUint64, whose spec gives any value.
func below(n int) int { return int(primitive.RandomUint64() % uint64(n)) }

// SyncRecorder is a raft.TraceLogger keeping every event in the order they are logged, from any
// goroutine.
type SyncRecorder struct {
	mu     sync.Mutex
	events []raft.TracingEvent
}

// TraceEvent records a copy of ev.
func (r *SyncRecorder) TraceEvent(ev *raft.TracingEvent) {
	r.mu.Lock()
	r.events = append(r.events, *ev)
	r.mu.Unlock()
}

// Events returns a copy of the events recorded so far.
func (r *SyncRecorder) Events() []raft.TracingEvent {
	r.mu.Lock()
	defer r.mu.Unlock()
	return append([]raft.TracingEvent(nil), r.events...)
}

// CConfig is a concurrent run's configuration.
type CConfig struct {
	Nodes      int // the bootstrap configuration's voters, ids 1..Nodes (StartNode)
	ExtraNodes int // empty nodes, ids Nodes+1..Nodes+ExtraNodes (RestartNode on empty storage)

	Proposals   int           // proposals, made one after another at random replicas
	ConfChanges int           // configuration changes (those the specification models), at the leader
	ProposeGap  time.Duration // the pause between two proposals
	Settle      time.Duration // how long the cluster runs after the last proposal

	Tick          time.Duration // the replicas' tick interval
	MaxDelay      time.Duration // a message's delay is uniform in [0, MaxDelay)
	DropPct       int           // percentage of messages dropped
	SnapshotEvery int           // as Config.SnapshotEvery (0: never)
	// Isolations: a driver cuts a random replica off the network (every message from or to it
	// dropped) for IsolateFor, that many times, one after another (0: never). Isolating the
	// leader makes the others elect another, while it stays leader of its term until it hears of
	// the next.
	Isolations int
	IsolateFor time.Duration
}

// DefaultCConfig is a small concurrent run: three voters, no configuration change or snapshot,
// three isolations (leader changes).
// Its timing is scaled to raft's `with_tla` build, which sleeps 1ms in every traced receipt
// (traceReceiveMessage, "to reduce time shift impact across node"): a run loop takes at least that
// per message, so a leader ticked every 2ms (a heartbeat to each follower per tick) falls behind
// and the network's Step times out.
func DefaultCConfig() CConfig {
	return CConfig{Nodes: 3, Proposals: 60, ProposeGap: 10 * time.Millisecond,
		Settle: 150 * time.Millisecond, Tick: 10 * time.Millisecond, MaxDelay: 10 * time.Millisecond, DropPct: 5,
		Isolations: 3, IsolateFor: 200 * time.Millisecond}
}

// FullCConfig is DefaultCConfig with a fourth node, configuration changes and snapshots.
func FullCConfig() CConfig {
	c := DefaultCConfig()
	c.ExtraNodes = 1
	c.ConfChanges = 4
	c.SnapshotEvery = 5
	return c
}

type creplica struct {
	id      uint64
	node    raft.Node
	storage *raft.MemoryStorage
	// the application goroutine's own
	applied, snapIndex uint64
	confState          *pb.ConfState
}

// Cluster is a concurrent run.
type Cluster struct {
	cfg      CConfig
	rec      *SyncRecorder
	replicas []*creplica
	stop     chan struct{}
	isolated atomic.Uint64  // the replica cut off the network now (0: none)
	apps     sync.WaitGroup // the application goroutines
	net      sync.WaitGroup // the network's goroutines

	Proposed, Delivered, Dropped, Readies, ConfChanges, Snapshots atomic.Int64
}

func (c *Cluster) replica(id uint64) *creplica {
	if id == 0 || id > uint64(len(c.replicas)) {
		return nil
	}
	return c.replicas[id-1]
}

// RunConcurrent runs a cluster: it starts the replicas and their goroutines, makes the proposals
// and configuration changes, lets the cluster settle, stops it, and returns it (its trace is
// Events).
func RunConcurrent(cfg CConfig) (*Cluster, error) {
	c := &Cluster{cfg: cfg, rec: &SyncRecorder{}, stop: make(chan struct{})}
	var peers []raft.Peer
	for i := 1; i <= cfg.Nodes; i++ {
		peers = append(peers, raft.Peer{ID: uint64(i)})
	}
	for i := 1; i <= cfg.Nodes+cfg.ExtraNodes; i++ {
		st := raft.NewMemoryStorage()
		rc := &raft.Config{
			ID:              uint64(i),
			ElectionTick:    10,
			HeartbeatTick:   1,
			Storage:         st,
			MaxSizePerMsg:   ^uint64(0), // no limit: a batch cut short carries a commit index past its last entry (notes/raft-trace-validation.md, item 5)
			MaxInflightMsgs: 256,
			Logger:          quietLogger{},
			TraceLogger:     c.rec,
		}
		var n raft.Node
		if i <= cfg.Nodes {
			n = raft.StartNode(rc, peers)
		} else {
			n = raft.RestartNode(rc)
		}
		c.replicas = append(c.replicas, &creplica{id: uint64(i), node: n, storage: st, confState: &pb.ConfState{}})
	}
	for _, r := range c.replicas {
		c.apps.Add(1)
		go c.app(r)
	}

	var drivers sync.WaitGroup
	drivers.Add(3)
	go func() { // the isolations
		defer drivers.Done()
		for k := 0; k < cfg.Isolations; k++ {
			time.Sleep(cfg.IsolateFor / 2)
			c.isolated.Store(uint64(1 + below(len(c.replicas))))
			time.Sleep(cfg.IsolateFor)
			c.isolated.Store(0)
		}
	}()
	go func() { // the proposer
		defer drivers.Done()
		for k := 1; k <= cfg.Proposals; k++ {
			r := c.replicas[below(len(c.replicas))]
			ctx, cancel := context.WithTimeout(context.Background(), 50*time.Millisecond)
			_ = r.node.Propose(ctx, []byte("v"+strconv.Itoa(k)))
			cancel()
			c.Proposed.Add(1)
			time.Sleep(cfg.ProposeGap)
		}
	}()
	go func() { // the proposer of configuration changes
		defer drivers.Done()
		deadline := time.Now().Add(time.Duration(cfg.Proposals) * cfg.ProposeGap)
		for int(c.ConfChanges.Load()) < cfg.ConfChanges && time.Now().Before(deadline) {
			time.Sleep(time.Duration(5+below(10)) * cfg.ProposeGap)
			for _, r := range c.replicas {
				st := r.node.Status()
				if cc := confChangeFor(st, len(c.replicas)); cc != nil {
					ctx, cancel := context.WithTimeout(context.Background(), 20*time.Millisecond)
					if r.node.ProposeConfChange(ctx, cc) == nil {
						c.ConfChanges.Add(1)
					}
					cancel()
					break
				}
			}
		}
	}()
	drivers.Wait()
	time.Sleep(cfg.Settle)

	close(c.stop)
	c.apps.Wait()
	for _, r := range c.replicas {
		r.node.Stop()
	}
	c.net.Wait()
	return c, nil
}

// Events returns the trace.
func (c *Cluster) Events() []raft.TracingEvent { return c.rec.Events() }

// confChangeFor is a configuration change for a leader of status st to propose that the
// specification models (as Sim.confChange), nil if st is not a leader's or no change applies.
func confChangeFor(st raft.Status, nodes int) *pb.ConfChange {
	if st.RaftState != raft.StateLeader || len(st.Config.Voters[1]) != 0 {
		return nil
	}
	target := uint64(1 + below(nodes))
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
		typ = []pb.ConfChangeType{pb.ConfChangeAddNode, pb.ConfChangeRemoveNode}[below(2)]
	default:
		typ = []pb.ConfChangeType{pb.ConfChangeAddNode, pb.ConfChangeAddLearnerNode}[below(2)]
	}
	return &pb.ConfChange{Type: typ.Enum(), NodeId: proto.Uint64(target)}
}

// app is replica r's application goroutine.
func (c *Cluster) app(r *creplica) {
	defer c.apps.Done()
	ticker := time.NewTicker(c.cfg.Tick)
	defer ticker.Stop()
	for {
		select {
		case <-c.stop:
			return
		case <-ticker.C:
			r.node.Tick()
		case rd := <-r.node.Ready():
			c.handleReady(r, rd)
			r.node.Advance()
			// The messages only now: Advance is a hand-off to the node's run loop, which takes it
			// once acceptReady has returned, so once the Ready is logged (traceReady is
			// acceptReady's last statement, after the Ready went to this goroutine): a message's
			// receipt is then logged after the Ready that hands it out, as the trace
			// specification needs (Ready(i) moves it from pendingMessages to messages).
			for _, m := range rd.Messages {
				c.send(r, proto.Clone(m).(*pb.Message), time.Duration(below(int(c.cfg.MaxDelay)+1)),
					below(100) < c.cfg.DropPct)
			}
		}
	}
}

// handleReady persists rd's snapshot, entries and hard state, applies its committed entries
// (configuration changes), and takes a snapshot when due (as Sim.ready); app sends rd's messages
// after Advance.
func (c *Cluster) handleReady(r *creplica, rd raft.Ready) {
	c.Readies.Add(1)
	if !raft.IsEmptySnap(rd.Snapshot) {
		if err := r.storage.ApplySnapshot(rd.Snapshot); err != nil {
			panic(err)
		}
		r.applied = rd.Snapshot.GetMetadata().GetIndex()
		r.snapIndex = r.applied
		r.confState = rd.Snapshot.GetMetadata().GetConfState()
	}
	if err := r.storage.Append(rd.Entries); err != nil {
		panic(err)
	}
	if rd.HardState != nil && !raft.IsEmptyHardState(rd.HardState) {
		if err := r.storage.SetHardState(rd.HardState); err != nil {
			panic(err)
		}
	}
	confApplied := false
	for _, e := range rd.CommittedEntries {
		switch e.GetType() {
		case pb.EntryConfChange:
			cc := &pb.ConfChange{}
			if err := proto.Unmarshal(e.GetData(), cc); err != nil {
				panic(err)
			}
			r.confState = r.node.ApplyConfChange(cc)
			confApplied = true
		case pb.EntryConfChangeV2:
			cc := &pb.ConfChangeV2{}
			if err := proto.Unmarshal(e.GetData(), cc); err != nil {
				panic(err)
			}
			r.confState = r.node.ApplyConfChange(cc)
			confApplied = true
		}
		r.applied = e.GetIndex()
	}
	if c.cfg.SnapshotEvery > 0 && r.applied > r.snapIndex &&
		(confApplied || r.applied >= r.snapIndex+uint64(c.cfg.SnapshotEvery)) {
		if _, err := r.storage.CreateSnapshot(r.applied, r.confState, nil); err != nil {
			panic(err)
		}
		if err := r.storage.Compact(r.applied); err != nil {
			panic(err)
		}
		r.snapIndex = r.applied
		c.Snapshots.Add(1)
	}
}

// stepTimeout bounds how long the network waits for a target to take a message (a target that
// does not take it in time has dropped it): a forwarded proposal blocks while its target knows no
// leader, and a message to a stopped node is never taken.
const stepTimeout = 50 * time.Millisecond

// send delivers m from src after delay, or drops it, from a goroutine of its own. The sender is
// told of a drop (ReportUnreachable) and of a snapshot's fate (ReportSnapshot).
func (c *Cluster) send(src *creplica, m *pb.Message, delay time.Duration, drop bool) {
	c.net.Add(1)
	go func() {
		defer c.net.Done()
		time.Sleep(delay)
		dst := c.replica(m.GetTo())
		typ, to := m.GetType(), m.GetTo()
		if iso := c.isolated.Load(); iso != 0 && (iso == to || iso == m.GetFrom()) {
			drop = true
		}
		delivered := false
		if dst != nil && !drop {
			ctx, cancel := context.WithTimeout(context.Background(), stepTimeout)
			delivered = dst.node.Step(ctx, m) == nil
			cancel()
		}
		if !delivered {
			c.Dropped.Add(1)
			src.node.ReportUnreachable(to)
			if typ == pb.MsgSnap {
				src.node.ReportSnapshot(to, raft.SnapshotFailure)
			}
			return
		}
		c.Delivered.Add(1)
		if typ == pb.MsgSnap {
			src.node.ReportSnapshot(to, raft.SnapshotFinish)
		}
	}()
}
