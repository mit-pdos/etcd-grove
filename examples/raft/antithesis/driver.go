package antithesis

import (
	"strconv"
	"sync"
	"time"

	pb "go.etcd.io/raft/v3/raftpb"
	"google.golang.org/protobuf/proto"

	"github.com/mit-pdos/etcd-grove/examples/raft/antithesis/check"
)

// ---------------------------------------------------------------------------------------------
// The scope and the run's mode.

// Scope is which features a run may have: Main draws each feature of its mode only where the
// scope allows it (DrawMode), so a theorem about Main is about every run within its scope. The
// features are the plan's (antithesis-parity-plan.md §2), grouped by the batch that proves them.
type Scope struct {
	// B1: messages and N servers.
	PreVote, CheckQuorum bool
	Reads, Transfer      bool
	Forwarding           bool // forwarded proposals (MsgProp) delivered; off: the network drops them
	Dup                  bool // the network may deliver a message twice
	NonVoters            bool // 5 servers of which 3 are the initial voters
	Boot                 bool // bootstrapped logs (BootInit)
	Limits               bool // MaxInflightMsgs and MaxSizePerMsg drawn; off: raft's usual 256, 1 MiB
	// B2: durability.
	Restarts, Async, Batch, Parallel, Split bool
	// B3: snapshots and membership (with ReportSnapshot, StepDownOnRemoval).
	Snapshots, ConfChanges bool
}

// Main's scope: one constant per feature. Flipping these constants is the only change to the
// program between the interim theorems; the plain theorem's scope has them all on. Here: batch B1's
// (messages and N servers; forwarding, and every B2/B3 feature, off).
const (
	scopePreVote     = true
	scopeCheckQuorum = true
	scopeReads       = true
	scopeTransfer    = true
	scopeForwarding  = false
	scopeDup         = true
	scopeNonVoters   = true
	scopeBoot        = true
	scopeLimits      = true
	scopeRestarts    = false
	scopeAsync       = false
	scopeBatch       = false
	scopeParallel    = false
	scopeSplit       = false
	scopeSnapshots   = false
	scopeConfChanges = false
)

// MainScope is Main's scope, from the constants above.
func MainScope() Scope {
	return Scope{PreVote: scopePreVote, CheckQuorum: scopeCheckQuorum, Reads: scopeReads, Transfer: scopeTransfer,
		Forwarding: scopeForwarding, Dup: scopeDup, NonVoters: scopeNonVoters, Boot: scopeBoot, Limits: scopeLimits,
		Restarts: scopeRestarts, Async: scopeAsync, Batch: scopeBatch, Parallel: scopeParallel, Split: scopeSplit,
		Snapshots: scopeSnapshots, ConfChanges: scopeConfChanges}
}

// Mode is what a run is: the binding's constants (Server, InitVoters, Bootstrapped) and the flags
// of Antithesis's simulator (antithesis-fm/sim/main.go: -nodes, -voters, -boot, -prevote,
// -checkquorum, -async, -parallel, -batch, -split, -inflight, -size, -snap, -snapstatus, -reads,
// -member, -transfer, -stepdown, -forward). Main draws it (DrawMode); every behaviour a flag leaves
// off is one its goroutine does not exercise in that run.
type Mode struct {
	Nodes  uint64 // the servers, ids 1..Nodes: 3 or 5
	Voters uint64 // the initial voters, ids 1..Voters: all, or 3
	Boot   bool   // every log starts with BootInit's entry (index 1, term 1), written before start

	PreVote, CheckQuorum bool
	StepDownOnRemoval    bool
	MaxInflightMsgs      uint64
	MaxSizePerMsg        uint64
	Forward              bool   // the network delivers forwarded proposals (MsgProp)
	MaxDeliveries        uint64 // a message is delivered 0 to MaxDeliveries times: 1, or 2 (Dup)

	Async    bool   // AsyncStorageWrites; the storage goroutine makes the writes
	Batch    bool   // a Ready (and a write) for several inputs; the flusher takes them
	Parallel bool   // sync, not batching: a leader sends its requests before its write
	Split    uint64 // sync, not batching: a Ready's state written in parts (split*)

	Reads       bool // the reader
	Transfer    bool // the transferer
	ConfChanges bool // the conf changer
	Snapshots   bool // the snapshotter (and so leaders send snapshots)
	SnapStatus  bool // the network reports each snapshot's fate (ReportSnapshot)
	Restarts    bool // the restarter

	// Anchor is an initial voter the conf changer never removes or demotes: raft panics when it
	// applies a change that leaves no voter (confchange: "removed all voters").
	Anchor uint64
}

// The write orders of Mode.Split (rawnode's Config.Split). DrawMode draws only the orders their
// model accepts: one atomic write, or term-entries-commit. The other two are kept for the tests
// that show what the model makes of them (harness_test.go, TestSplitOrders):
//   - splitHardStateEntries writes the HardState before the entries, against raft's documented
//     order (README.md: "Entries first, then HardState"); the model rejects the first write of a
//     follower answering a request to append (new commit index, no entries yet), with no kill
//     (their own simulator's streams too, 30 of 30 seeds, checked by package check);
//   - splitEntriesHardState is raft's README order; the model rejects a write of entries of a newer
//     term than the HardState on disk (a follower's first append in a new term: the term comes
//     in the second write), a state it has no counterpart for, with no kill (their simulator: 5
//     of 30 seeds): a model limitation (plan §2).
const (
	splitNone uint64 = iota
	splitTermEntriesCommit
	splitHardStateEntries
	splitEntriesHardState
)

func coin() bool { return below(2) == 0 }

// may is a feature the scope allows (on), drawn at random.
func may(on bool) bool { return on && coin() }

// DrawMode draws a run's mode within scope s, every flag at random, within what rawnode allows:
// batching neither with Split nor with Parallel; Parallel and Split only for synchronous storage,
// where rawnode uses them; Split one of the orders their model accepts. MaxInflightMsgs and
// MaxSizePerMsg are drawn from the simulator's values (inflight: 1, 2 or raft's usual 256; size:
// one entry per message, 64 bytes, or 1 MiB).
func DrawMode(s Scope) Mode {
	m := Mode{MaxInflightMsgs: 256, MaxSizePerMsg: 1 << 20, MaxDeliveries: 1}
	m.Nodes = 3 + 2*below(2)
	m.Voters = m.Nodes
	if m.Nodes == 5 && may(s.NonVoters) {
		m.Voters = 3
	}
	m.Boot = may(s.Boot)
	m.PreVote, m.CheckQuorum = may(s.PreVote), may(s.CheckQuorum)
	if s.Limits {
		m.MaxInflightMsgs = []uint64{1, 2, 256}[below(3)]
		m.MaxSizePerMsg = []uint64{0, 64, 1 << 20}[below(3)]
	}
	m.Forward = may(s.Forwarding)
	if may(s.Dup) {
		m.MaxDeliveries = 2
	}
	m.Async, m.Batch = may(s.Async), may(s.Batch)
	if !m.Async && !m.Batch {
		m.Parallel = may(s.Parallel)
		if may(s.Split) {
			m.Split = splitTermEntriesCommit
		}
	}
	m.Reads, m.Transfer, m.Restarts = may(s.Reads), may(s.Transfer), may(s.Restarts)
	m.Snapshots, m.ConfChanges = may(s.Snapshots), may(s.ConfChanges)
	m.SnapStatus = m.Snapshots && coin()
	m.StepDownOnRemoval = m.ConfChanges && coin()
	m.Anchor = 1 + below(m.Voters)
	return m
}

// ---------------------------------------------------------------------------------------------
// The cluster.

// Config is a run's pacing: how long it runs and how often each behaviour acts. Any values give
// a run the theorem covers; they are there so that a real run does something before it stops.
type Config struct {
	Settle      time.Duration // how long the cluster runs before it is stopped
	Tick        time.Duration // the nodes' tick interval; positive (time.NewTicker panics otherwise)
	Pace        time.Duration // the period of each behaviour's goroutine
	RestartPace time.Duration // the restarter's period: a node is down for about this long
	// ElectionPace: the campaigner's and the transferer's period. An election takes a few
	// rounds of writes and messages (with Async, the storage's steps): elections started more
	// often than that keep any leader from committing.
	ElectionPace time.Duration
	// NoHoldVote: with Async, a request for votes is sent at once instead of after its write
	// (raft as forked, without their E1 patch). Only for the reproducer test; Main leaves it off.
	NoHoldVote bool
}

// DefaultConfig is Main's pacing: ticks every 2ms (a follower campaigns after 10 to 20 ticks
// without a leader), a behaviour every millisecond, an election or a transfer every 20ms, a
// restart every 40ms, for 150ms.
func DefaultConfig() Config {
	return Config{Settle: 150 * time.Millisecond, Tick: 2 * time.Millisecond, Pace: time.Millisecond,
		ElectionPace: 20 * time.Millisecond, RestartPace: 40 * time.Millisecond}
}

// raft's configuration of every node (beyond the mode's), and the harness's sizes.
const (
	electionTick             = 10      // ticks without a leader before a follower campaigns (raft's usual)
	heartbeatTick            = 1       // a leader's heartbeat every tick (raft's usual 1)
	maxCommittedSizePerReady = 1 << 20 // bytes of committed entries per Ready (rawnode's)
	inboxSize                = 1024    // a node's input channel buffer: senders block only when it is full
)

// input kinds: each is one call of the client API on the node's goroutine.
const (
	inMsg         uint64 = iota // RawNode.Step of a message from the network
	inProp                      // Propose
	inConf                      // ProposeConfChange (a change drawn from the node's configuration)
	inRead                      // ReadIndex
	inTransfer                  // TransferLeader
	inCampaign                  // Campaign
	inSnapStatus                // ReportSnapshot
	inUnreachable               // ReportUnreachable
	inSnapshot                  // CreateSnapshot + Compact at the applied index
	inFlush                     // Batch: take the Ready
	inWork                      // Async: one storage step
	inKill                      // kill the node: now, or at one of its next reports
)

// input is one input to a node.
type input struct {
	kind uint64
	msg  *pb.Message
	data []byte
	to   uint64
	ok   bool
}

// Cluster is a run.
type Cluster struct {
	cfg        Config
	mode       Mode
	rec        *Recorder
	nodes      []*node
	initVoters []uint64
	stop       chan struct{}

	mu   sync.Mutex
	down []bool // the node's goroutine has stopped (it was killed) and not been restarted

	nodesWg sync.WaitGroup // the nodes' goroutines
	netWg   sync.WaitGroup // the network's goroutines
	behWg   sync.WaitGroup // the behaviours' goroutines
}

func (c *Cluster) node(id uint64) *node {
	if id == 0 || id > uint64(len(c.nodes)) {
		return nil
	}
	return c.nodes[id-1]
}

// pick is a random node.
func (c *Cluster) pick() *node { return c.nodes[below(c.mode.Nodes)] }

// Events is the stream.
func (c *Cluster) Events() []*check.Event { return c.rec.Events() }

// CheckConfig is the binding's constants for the run: Server, InitVoters, Bootstrapped.
func (c *Cluster) CheckConfig() *check.Config {
	return &check.Config{Server: check.SetOf(names(c.mode.Nodes)), InitVoters: check.SetOf(names(c.mode.Voters)),
		Bootstrapped: c.mode.Boot}
}

// RunCluster runs a cluster in mode: it starts the nodes and the behaviours, lets them run for
// Settle, stops them, and returns the cluster (its stream is Events).
func RunCluster(cfg Config, mode Mode) *Cluster {
	c := &Cluster{cfg: cfg, mode: mode, rec: &Recorder{}, stop: make(chan struct{})}
	for i := uint64(1); i <= mode.Voters; i++ {
		c.initVoters = append(c.initVoters, i)
	}
	for i := uint64(1); i <= mode.Nodes; i++ {
		n := &node{c: c, id: i, name: Name(i), in: make(chan input, inboxSize), disk: &disk{hs: &pb.HardState{}}}
		c.nodes = append(c.nodes, n)
		c.down = append(c.down, false)
	}
	for _, n := range c.nodes {
		c.nodesWg.Add(1)
		go c.run(n)
	}
	c.spawn(c.proposer)
	c.spawn(c.campaigner)
	if mode.Reads {
		c.spawn(c.reader)
	}
	if mode.Transfer {
		c.spawn(c.transferer)
	}
	if mode.ConfChanges {
		c.spawn(c.confChanger)
	}
	if mode.Snapshots {
		c.spawn(c.snapshotter)
	}
	if mode.Restarts {
		c.spawn(c.restarter)
	}
	if mode.Batch {
		c.spawn(c.flusher)
	}
	if mode.Async {
		c.spawn(c.storage)
	}
	time.Sleep(cfg.Settle)

	close(c.stop)
	c.behWg.Wait()
	c.nodesWg.Wait()
	c.netWg.Wait()
	return c
}

func (c *Cluster) spawn(f func()) {
	c.behWg.Add(1)
	go func() {
		f()
		c.behWg.Done()
	}()
}

// running waits for d and says whether the run goes on.
func (c *Cluster) running(d time.Duration) bool {
	time.Sleep(d)
	select {
	case <-c.stop:
		return false
	default:
		return true
	}
}

// deliver hands inp to n, unless the run stops first. A node that is down takes nothing until it
// is restarted.
func (c *Cluster) deliver(n *node, inp input) {
	select {
	case n.in <- inp:
	case <-c.stop:
	}
}

// ---------------------------------------------------------------------------------------------
// The node's goroutine.

// run is node n's goroutine: it starts the node from its disk, then takes one input at a time,
// each followed by its Readies, until the run stops or the node dies (a kill: its memory is
// dropped with the goroutine; what is on its disk stays, for the restarter).
func (c *Cluster) run(n *node) {
	n.start()
	ticker := time.NewTicker(c.cfg.Tick)
	for !n.dead {
		select {
		case <-c.stop:
			ticker.Stop()
			c.nodesWg.Done()
			return
		case <-ticker.C:
			n.tick()
		case inp := <-n.in:
			c.handle(n, inp)
		}
	}
	ticker.Stop()
	c.mu.Lock()
	c.down[n.id-1] = true
	c.mu.Unlock()
	c.nodesWg.Done()
}

func (c *Cluster) handle(n *node, inp input) {
	k := inp.kind
	if k == inMsg {
		n.step(inp.msg)
	} else if k == inProp {
		n.propose(inp.data)
	} else if k == inConf {
		n.proposeConfChange(c.change(n))
	} else if k == inRead {
		n.readIndex(string(inp.data))
	} else if k == inTransfer {
		n.transferLeader(inp.to)
	} else if k == inCampaign {
		n.campaign()
	} else if k == inSnapStatus {
		n.snapshotStatus(inp.to, inp.ok)
	} else if k == inUnreachable {
		n.unreachable(inp.to)
	} else if k == inSnapshot {
		n.snapshot(n.applied)
	} else if k == inFlush {
		n.flush()
	} else if k == inWork {
		n.work()
	} else if k == inKill {
		// Now, or at one of the node's next reports (1 to 6; rawnode's simulator's fuse), and then
		// possibly between a write's announcement and the write.
		if coin() {
			n.dead = true
		} else {
			n.fuse = 1 + below(6)
		}
	}
}

// restart starts a new goroutine for node n, if it is down.
func (c *Cluster) restart(n *node) {
	c.mu.Lock()
	if c.down[n.id-1] {
		c.down[n.id-1] = false
		c.nodesWg.Add(1)
		go c.run(n)
	}
	c.mu.Unlock()
}

// ---------------------------------------------------------------------------------------------
// The network.

// send delivers m from a goroutine of its own, 0 to Mode.MaxDeliveries times (lost, or with Dup
// duplicated: the most permissive network, plan decision 3), in any order with other messages. A message
// delivered no time is reported to its sender as unreachable (ReportUnreachable); with
// Mode.SnapStatus, a snapshot's fate is reported to its sender (ReportSnapshot). A forwarded
// proposal (MsgProp) is dropped unless Mode.Forward (the first harness's choice,
// notes/antithesis-s4-design.md §7).
func (c *Cluster) send(m *pb.Message) {
	if m.GetType() == pb.MessageType_MsgProp && !c.mode.Forward {
		return
	}
	c.netWg.Add(1)
	go func() {
		k := below(c.mode.MaxDeliveries + 1)
		dst := c.node(m.GetTo())
		src := c.node(m.GetFrom())
		if dst != nil {
			for j := uint64(0); j < k; j++ {
				c.deliver(dst, input{kind: inMsg, msg: proto.Clone(m).(*pb.Message)})
			}
		}
		if src != nil && k == 0 {
			c.deliver(src, input{kind: inUnreachable, to: m.GetTo()})
		}
		if src != nil && c.mode.SnapStatus && m.GetType() == pb.MessageType_MsgSnap {
			c.deliver(src, input{kind: inSnapStatus, to: m.GetTo(), ok: k > 0})
		}
		c.netWg.Done()
	}()
}

// ---------------------------------------------------------------------------------------------
// The behaviours: one goroutine each, calling the client API on random nodes until the run stops.

// The proposer: proposals "v1", "v2", ... (Propose) to random nodes; a follower forwards one to
// its leader. Exercises: every committed entry is the same on every node (the binding's chain).
func (c *Cluster) proposer() {
	for k := uint64(1); c.running(c.cfg.Pace); k++ {
		c.deliver(c.pick(), input{kind: inProp, data: []byte("v" + strconv.FormatUint(k, 10))})
	}
}

// The campaigner: Campaign on random nodes. Exercises: at most one leader per term
// (ElectionSafety), whoever starts an election and whenever.
func (c *Cluster) campaigner() {
	for c.running(c.cfg.ElectionPace) {
		c.deliver(c.pick(), input{kind: inCampaign})
	}
}

// The reader: ReadIndex with contexts "r1", "r2", ... on random nodes. Exercises: a read index
// covers every entry committed before the read was asked (ReadIndexStale).
func (c *Cluster) reader() {
	for k := uint64(1); c.running(c.cfg.Pace); k++ {
		c.deliver(c.pick(), input{kind: inRead, data: []byte("r" + strconv.FormatUint(k, 10))})
	}
}

// The transferer: TransferLeader to a random node, on random nodes. Exercises: a handed-over
// leadership keeps every committed entry (the chain) and one leader per term.
func (c *Cluster) transferer() {
	for c.running(c.cfg.ElectionPace) {
		c.deliver(c.pick(), input{kind: inTransfer, to: 1 + below(c.mode.Nodes)})
	}
}

// The conf changer: ProposeConfChange on random nodes, of a change drawn from the node's
// configuration (change); the nodes apply the committed ones (ApplyConfChange, switchConf).
// Exercises: elections and commits stay safe while the voters change (joint configurations,
// learners, V1 and V2 changes).
func (c *Cluster) confChanger() {
	for c.running(c.cfg.Pace) {
		c.deliver(c.pick(), input{kind: inConf})
	}
}

// The snapshotter: random nodes put a snapshot of what they applied in place of their log
// (CreateSnapshot and Compact at the applied index), so leaders send snapshots (MsgSnap) to
// nodes behind. Exercises: a restored snapshot is the chain's prefix.
func (c *Cluster) snapshotter() {
	for c.running(c.cfg.Pace) {
		c.deliver(c.pick(), input{kind: inSnapshot})
	}
}

// The restarter: kills a random node (now, or at one of its next reports, possibly between a
// write's announcement and the write), and restarts every node that is down from what is on its
// disk. Exercises: a node recovers its durable state, and loses only what it never wrote.
func (c *Cluster) restarter() {
	for c.running(c.cfg.RestartPace) {
		c.deliver(c.pick(), input{kind: inKill})
		if !c.running(c.cfg.RestartPace) {
			return
		}
		for _, n := range c.nodes {
			c.restart(n)
		}
	}
}

// The flusher (Mode.Batch): each node takes its Ready, for every input since the last one.
func (c *Cluster) flusher() {
	for c.running(c.cfg.Pace) {
		for _, n := range c.nodes {
			c.deliver(n, input{kind: inFlush})
		}
	}
}

// The storage (Mode.Async): each node takes one step of its queued storage work (work).
func (c *Cluster) storage() {
	for c.running(c.cfg.Pace) {
		for _, n := range c.nodes {
			c.deliver(n, input{kind: inWork})
		}
	}
}

// change is a change of membership to propose on node n, drawn as rawnode's simulator draws it
// (sim's `change`), from the configuration n counts with: leaving a joint configuration (an empty
// ConfChangeV2, Transition Auto: another Transition panics raft on apply, their patches/README.md
// E4), a V1 change of one node, a V2 change of one node, or a joint change of 1 to 3 nodes with
// any Transition. A node is added, removed, or made a learner; never the anchor removed.
func (c *Cluster) change(n *node) pb.ConfChangeI {
	cs := n.conf
	if (len(cs.GetVotersOutgoing()) > 0 && coin()) || below(12) == 0 {
		return &pb.ConfChangeV2{}
	}
	used := make([]bool, c.mode.Nodes+1)
	k := below(10)
	if k < 2 {
		ch := c.changeOne(cs, used)
		return &pb.ConfChange{Type: ch.Type, NodeId: ch.NodeId}
	}
	if k < 6 {
		return &pb.ConfChangeV2{Changes: []*pb.ConfChangeSingle{c.changeOne(cs, used)}}
	}
	cc := &pb.ConfChangeV2{}
	count := 1 + below(3)
	for j := uint64(0); j < count; j++ {
		cc.Changes = append(cc.Changes, c.changeOne(cs, used))
	}
	tr := []pb.ConfChangeTransition{pb.ConfChangeTransitionAuto, pb.ConfChangeTransitionJointImplicit,
		pb.ConfChangeTransitionJointExplicit}[below(3)]
	cc.Transition = tr.Enum()
	return cc
}

// changeOne is one node's change, of a node not yet in used: a voter is removed or made a learner
// (or re-added), a node that is not a voter is added, made a learner or removed (sim's `one`).
func (c *Cluster) changeOne(cs *pb.ConfState, used []bool) *pb.ConfChangeSingle {
	id := 1 + below(c.mode.Nodes)
	for used[id] {
		id = 1 + below(c.mode.Nodes)
	}
	used[id] = true
	voter := false
	for _, v := range cs.GetVoters() {
		if v == id {
			voter = true
		}
	}
	t := pb.ConfChangeAddNode
	k := below(10)
	if id == c.mode.Anchor {
	} else if voter && k < 7 {
		t = pb.ConfChangeRemoveNode
	} else if (voter && k < 8) || (!voter && k < 2) {
		t = pb.ConfChangeAddLearnerNode
	} else if !voter && k < 3 {
		t = pb.ConfChangeRemoveNode
	}
	return &pb.ConfChangeSingle{Type: t.Enum(), NodeId: u64p(id)}
}
