package kvreconf

import (
	"context"
	"fmt"
	"sync"
	"sync/atomic"
	"time"

	"github.com/goose-lang/primitive"
	"github.com/mit-pdos/gokv/trusted_proph"
	"go.etcd.io/raft/v3"
	pb "go.etcd.io/raft/v3/raftpb"
	"google.golang.org/protobuf/proto"
)

// quietLogger is a raft.Logger that discards what raft logs; Fatal and Panic panic, as raft
// expects of them.
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

// Stats counts what a run exercised (per replica: an entry applied by three replicas counts
// three times). It is for the tests' coverage checks; the store does not read it.
type Stats struct {
	SnapshotsTaken             atomic.Uint64
	SnapshotsTakenJoint        atomic.Uint64 // at a joint configuration
	SnapshotsSent              atomic.Uint64
	SnapshotsInstalled         atomic.Uint64
	SnapshotsInstalledJoint    atomic.Uint64
	SnapshotsInstalledLearners atomic.Uint64
	Compactions                atomic.Uint64
	ConfChangesProposed        atomic.Uint64
	ConfChangesApplied         atomic.Uint64
	ConfChangesRejected        atomic.Uint64 // committed but invalid where applied
	JointEntered               atomic.Uint64
	ReplicasStarted            atomic.Uint64
	Dropped                    atomic.Uint64
	Duplicated                 atomic.Uint64
	Delayed                    atomic.Uint64
	Retries                    atomic.Uint64
}

func (s *Stats) add(c *atomic.Uint64) { c.Add(1) }

func (s *Stats) String() string {
	return fmt.Sprintf("snapshots taken %d (%d joint), sent %d, installed %d (%d joint, %d with learners), compactions %d; "+
		"conf changes proposed %d, applied %d, rejected %d, joint entered %d; replicas started %d; "+
		"messages dropped %d, duplicated %d, delayed %d; client retries %d",
		s.SnapshotsTaken.Load(), s.SnapshotsTakenJoint.Load(), s.SnapshotsSent.Load(), s.SnapshotsInstalled.Load(),
		s.SnapshotsInstalledJoint.Load(), s.SnapshotsInstalledLearners.Load(), s.Compactions.Load(),
		s.ConfChangesProposed.Load(), s.ConfChangesApplied.Load(), s.ConfChangesRejected.Load(), s.JointEntered.Load(),
		s.ReplicasStarted.Load(), s.Dropped.Load(), s.Duplicated.Load(), s.Delayed.Load(), s.Retries.Load())
}

// hasID says whether id is in ids.
func hasID(ids []uint64, id uint64) bool {
	for _, x := range ids {
		if x == id {
			return true
		}
	}
	return false
}

// Options are a cluster's size and raft's options.
type Options struct {
	Voters            uint64 // the bootstrap configuration's, 1 to 5
	PreVote           bool
	CheckQuorum       bool
	StepDownOnRemoval bool
	MaxSizePerMsg     uint64
	// MaxCommittedSizePerReady is never 0 when MaxSizePerMsg is: raft defaults the former to the
	// latter, and panics with both 0 (issues/nonissues/raft-zero-max-size-per-msg.md; the
	// premise of raft's NewRawNode and RestartNode specs)
	MaxCommittedSizePerReady uint64
	MaxInflightMsgs          int
}

// RandomOptions are options chosen at random.
func RandomOptions() Options {
	o := Options{
		Voters:            1 + below(5),
		PreVote:           oneIn(2),
		CheckQuorum:       oneIn(2),
		StepDownOnRemoval: oneIn(2),
		MaxSizePerMsg:     []uint64{0, 256, 4 << 10, 1 << 20}[below(4)],
		MaxInflightMsgs:   []int{1, 4, 256}[below(3)],
	}
	o.MaxCommittedSizePerReady = []uint64{0, 4 << 10, 1 << 20}[below(3)]
	if o.MaxSizePerMsg == 0 && o.MaxCommittedSizePerReady == 0 {
		o.MaxCommittedSizePerReady = 4 << 10
	}
	return o
}

// maxReplicas bounds the replicas a cluster starts (removed ones keep running).
const maxReplicas = 9

// Cluster is a cluster of replicas connected in process: every replica it started (removed
// ones keep running: they may be added back), the next fresh id and operation id, and the
// statistics.
type Cluster struct {
	opts  Options
	Stats Stats

	boot     *pb.ConfState // the bootstrap configuration: every replica's before it applies anything
	mu       sync.Mutex
	replicas map[uint64]*Replica
	nextID   uint64
	nextOp   uint64
}

// StartCluster starts a cluster of opts.Voters voters, of ids 1 to opts.Voters: each a
// raft.RestartNode on an empty storage whose initial configuration is the bootstrap one (the
// voters), as a newcomer's (startNew); the log starts empty and the first leader is elected from
// that configuration.
func StartCluster(opts Options) *Cluster {
	c := &Cluster{opts: opts, replicas: make(map[uint64]*Replica), nextID: opts.Voters + 1, boot: &pb.ConfState{}}
	for id := uint64(1); id <= opts.Voters; id++ {
		c.boot.Voters = append(c.boot.Voters, id)
	}
	c.mu.Lock()
	for id := uint64(1); id <= opts.Voters; id++ {
		st := &Storage{MemoryStorage: raft.NewMemoryStorage(), boot: c.boot}
		c.replicas[id] = newReplica(id, raft.RestartNode(c.config(id, st)), st, c.boot, c.tick(), &c.Stats, c.sender(id))
		c.Stats.add(&c.Stats.ReplicasStarted)
	}
	c.mu.Unlock()
	return c
}

// tick is a random tick interval, 1 to 4ms: the replicas' clocks run at different rates.
func (c *Cluster) tick() time.Duration {
	return time.Duration(1+below(4)) * time.Millisecond
}

// config is raft's configuration of node id on storage st.
func (c *Cluster) config(id uint64, st *Storage) *raft.Config {
	return &raft.Config{
		ID:                       id,
		ElectionTick:             10,
		HeartbeatTick:            1,
		Storage:                  st,
		MaxSizePerMsg:            c.opts.MaxSizePerMsg,
		MaxCommittedSizePerReady: c.opts.MaxCommittedSizePerReady,
		MaxInflightMsgs:          c.opts.MaxInflightMsgs,
		Logger:                   quietLogger{},
		PreVote:                  c.opts.PreVote,
		CheckQuorum:              c.opts.CheckQuorum,
		StepDownOnRemoval:        c.opts.StepDownOnRemoval,
	}
}

// startNew starts a replica of a fresh id that is in no configuration yet (raft.RestartNode on
// an empty storage whose initial configuration is the bootstrap's: it waits for a leader to send
// it the log or a snapshot) and returns its id;
// ok is false if the cluster has started maxReplicas already.
func (c *Cluster) startNew() (uint64, bool) {
	c.mu.Lock()
	defer c.mu.Unlock()
	if len(c.replicas) >= maxReplicas {
		return 0, false
	}
	id := c.nextID
	c.nextID++
	st := &Storage{MemoryStorage: raft.NewMemoryStorage(), boot: c.boot}
	c.replicas[id] = newReplica(id, raft.RestartNode(c.config(id, st)), st, c.boot, c.tick(), &c.Stats, c.sender(id))
	c.Stats.add(&c.Stats.ReplicasStarted)
	return id, true
}

// all is every replica, in no particular order.
func (c *Cluster) all() []*Replica {
	c.mu.Lock()
	defer c.mu.Unlock()
	var rs []*Replica
	for _, r := range c.replicas {
		rs = append(rs, r)
	}
	return rs
}

// random is a random replica.
func (c *Cluster) random() *Replica {
	rs := c.all()
	return rs[below(uint64(len(rs)))]
}

// replica is replica id, or nil.
func (c *Cluster) replica(id uint64) *Replica {
	c.mu.Lock()
	defer c.mu.Unlock()
	return c.replicas[id]
}

// randomMember is a random member (voter or learner) of a random replica's configuration, or,
// one time in four or if that has none, a random replica.
func (c *Cluster) randomMember() *Replica {
	cs, _ := c.random().conf()
	members := append(append([]uint64(nil), cs.GetVoters()...), cs.GetLearners()...)
	if len(members) == 0 || oneIn(4) {
		return c.random()
	}
	if r := c.replica(members[below(uint64(len(members)))]); r != nil {
		return r
	}
	return c.random()
}

// sender is the transport of replica from's messages.
func (c *Cluster) sender(from uint64) func([]*pb.Message) {
	return func(ms []*pb.Message) { c.send(from, ms) }
}

// send hands each message of replica from to the network (deliver), each as a fresh copy (the
// wire's: copyMsg).
func (c *Cluster) send(from uint64, ms []*pb.Message) {
	src := c.replica(from)
	for _, m := range ms {
		c.deliver(src, copyMsg(m))
	}
}

// copyMsg is a fresh copy of m, as the wire delivers it: a new message with m's fields, a new
// Entries slice of m's entries, and a deep copy of its snapshot. It shares with m what neither
// raft nor the network ever writes: the fields' values (each field is a pointer to its value),
// the entries and the Context bytes. It leaves out m's Responses, which only a message a node
// sends itself has (never one in a Ready's Messages, with synchronous storage writes). Unlike
// proto.Clone, it does not copy the entries, so its proof needs no model of the message's wire
// encoding.
func copyMsg(m *pb.Message) *pb.Message {
	c := &pb.Message{Type: m.Type, To: m.To, From: m.From, Term: m.Term, LogTerm: m.LogTerm,
		Index: m.Index, Commit: m.Commit, Vote: m.Vote, Reject: m.Reject, RejectHint: m.RejectHint,
		Context: m.Context, Entries: append([]*pb.Entry(nil), m.Entries...)}
	if m.Snapshot != nil {
		c.Snapshot = proto.Clone(m.Snapshot).(*pb.Snapshot)
	}
	return c
}

// stepTimeout bounds how long the network waits for a target to take a message: Step of a
// forwarded proposal (MsgProp) blocks while the target knows no leader, and a sender must not
// wait for that (a candidate whose loop is blocked never handles the Ready that persists its
// vote, so never receives it: a cluster whose only voter it is would never elect anyone).
const stepTimeout = 5 * time.Millisecond

// deliver is the network: it drops the message (one time in twenty), or delivers it later, from
// another goroutine (one time in eight: messages are reordered), or now; a message delivered
// may be delivered a second time (one time in thirty-two). A message to a replica that does
// not exist, or that its target does not take within stepTimeout, is dropped. The sender is
// told of a drop (Node.ReportUnreachable) and of each snapshot's fate (Node.ReportSnapshot:
// a leader waits for it before it sends the follower anything else), which the network may
// also report as failed when it was delivered.
func (c *Cluster) deliver(src *Replica, m *pb.Message) {
	dst := c.replica(m.GetTo())
	if dst == nil || oneIn(20) {
		c.dropped(src, m)
		return
	}
	if oneIn(8) {
		c.Stats.add(&c.Stats.Delayed)
		delay := time.Duration(below(20)) * time.Millisecond
		go func() {
			time.Sleep(delay)
			c.step(src, dst, m)
		}()
		return
	}
	var dup *pb.Message
	if oneIn(32) {
		dup = copyMsg(m)
	}
	c.step(src, dst, m)
	if dup != nil {
		c.Stats.add(&c.Stats.Duplicated)
		c.step(src, dst, dup)
	}
}

// step steps m on its target dst and reports a snapshot's fate to its sender src. It reads m
// only before stepping it: the target keeps the message and writes it (`Node.Step` sets its
// `From`, a forward sets its `To`: issues/nonissues/raft-step-writes-caller-message.md).
func (c *Cluster) step(src, dst *Replica, m *pb.Message) {
	typ, to := m.GetType(), m.GetTo()
	ctx, cancel := context.WithTimeout(context.Background(), stepTimeout)
	err := dst.node.Step(ctx, m)
	cancel()
	// not taken (timed out, or the target stopped): dropped. (Not `err == context.DeadlineExceeded`:
	// comparing two interfaces needs their dynamic type comparable, which the proof cannot see of
	// context's error values; and a stopped target has not taken the message either.)
	if err != nil {
		c.Stats.add(&c.Stats.Dropped)
		src.node.ReportUnreachable(to)
		if typ == pb.MsgSnap {
			src.node.ReportSnapshot(to, raft.SnapshotFailure)
		}
		return
	}
	if typ == pb.MsgSnap {
		c.Stats.add(&c.Stats.SnapshotsSent)
		if oneIn(8) {
			src.node.ReportSnapshot(to, raft.SnapshotFailure)
		} else {
			src.node.ReportSnapshot(to, raft.SnapshotFinish)
		}
	}
}

// dropped tells the sender of a dropped message so.
func (c *Cluster) dropped(src *Replica, m *pb.Message) {
	c.Stats.add(&c.Stats.Dropped)
	src.node.ReportUnreachable(m.GetTo())
	if m.GetType() == pb.MsgSnap {
		src.node.ReportSnapshot(m.GetTo(), raft.SnapshotFailure)
	}
}

// opTimeout is how long a client waits for an answer at one replica before it tries another.
const opTimeout = 100 * time.Millisecond

// do runs one operation through the log: it gives it a fresh id and proposes it at a random
// member until one answers (the same encoding each time: it takes effect once).
func (c *Cluster) do(kind byte, key, val string) string {
	c.mu.Lock()
	if c.nextOp == maxSeq {
		// every operation id used (2^64 - 1 operations): it does not happen
		c.mu.Unlock()
		for {
		}
	}
	c.nextOp++
	op := encode(c.nextOp, kind, key, val)
	c.mu.Unlock()
	for {
		if v, ok := c.randomMember().propose(op, opTimeout); ok {
			return v
		}
		c.Stats.add(&c.Stats.Retries)
	}
}

// Put sets key's value to val.
func (c *Cluster) Put(key, val string) {
	c.do(opPut, key, val)
}

// Get returns key's value ("" for a key never set), through the log.
func (c *Cluster) Get(key string) string {
	return c.do(opGet, key, "")
}

// Read returns key's value by a read index at a random member, retried at another until one
// answers (a read has no effect: each attempt is a fresh one). The prophecy p, resolved with the
// answer, is for the proof only (it tells the proof, at each change of the store, whether the
// key's value then is the answer: the read's linearization point); it has no effect.
func (c *Cluster) Read(key string) string {
	p := primitive.NewProph()
	for {
		if v, ok := c.randomMember().read(key, opTimeout); ok {
			trusted_proph.ResolveBytes(p, []byte(v))
			return v
		}
		c.Stats.add(&c.Stats.Retries)
	}
}

// Stop stops every replica.
func (c *Cluster) Stop() {
	for _, r := range c.all() {
		r.stop()
	}
}

// Converged waits up to timeout for the members of the configuration of the replica that has
// applied the most to agree with it: the same applied index, the same configuration and the
// same store contents. It returns an error describing the disagreement otherwise.
func (c *Cluster) Converged(timeout time.Duration) error {
	deadline := time.Now().Add(timeout)
	for {
		err := c.agree()
		if err == nil || time.Now().After(deadline) {
			return err
		}
		time.Sleep(10 * time.Millisecond)
	}
}

// agree is Converged's check, once.
func (c *Cluster) agree() error {
	var top *Replica
	var topIndex uint64
	for _, r := range c.all() {
		if _, i := r.conf(); top == nil || i > topIndex {
			top, topIndex = r, i
		}
	}
	cs, _ := top.conf()
	kv0, i0 := top.contents()
	members := append(append(append([]uint64(nil), cs.GetVoters()...), cs.GetVotersOutgoing()...), cs.GetLearners()...)
	for _, id := range members {
		r := c.replica(id)
		if r == nil {
			return fmt.Errorf("kvreconf: member %d does not exist", id)
		}
		kv, i := r.contents()
		rcs, _ := r.conf()
		if i != i0 {
			return fmt.Errorf("kvreconf: replica %d applied %d, member %d applied %d", top.id, i0, id, i)
		}
		if !proto.Equal(cs, rcs) {
			return fmt.Errorf("kvreconf: replica %d's configuration %v, member %d's %v", top.id, cs, id, rcs)
		}
		if !within(kv, kv0) || !within(kv0, kv) {
			return fmt.Errorf("kvreconf: replicas %d and %d differ at index %d: %v, %v", top.id, id, i, kv0, kv)
		}
	}
	return nil
}

// Dump describes every replica's raft state, for a test that fails: its role, term, leader,
// commit and applied indices, configuration, log's first and last indices and latest
// snapshot, and, for a leader, its followers' progress.
func (c *Cluster) Dump() string {
	s := ""
	for _, r := range c.all() {
		st := r.node.Status()
		first, _ := r.storage.FirstIndex()
		last, _ := r.storage.LastIndex()
		snap, _ := r.storage.MemoryStorage.Snapshot()
		s += fmt.Sprintf("%d: %v term %d lead %d commit %d applied %d cfg %v log [%d, %d] snapshot %d (%v)\n",
			r.id, st.RaftState, st.HardState.GetTerm(), st.Lead, st.HardState.GetCommit(), st.Applied, st.Config,
			first, last, snap.GetMetadata().GetIndex(), snap.GetMetadata().GetConfState())
		for id, pr := range st.Progress {
			s += fmt.Sprintf("    %d: %v\n", id, pr.String())
		}
	}
	return s
}
