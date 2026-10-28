package kvreconf

import (
	"context"
	"fmt"
	"sync"
	"sync/atomic"
	"time"

	"github.com/goose-lang/primitive"
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

// Stats counts what a run exercised.
type Stats struct {
	SnapshotsTaken        atomic.Uint64
	SnapshotsSent         atomic.Uint64
	SnapshotsInstalled    atomic.Uint64
	SnapshotsReconfigured atomic.Uint64 // installed with a configuration other than the bootstrap's
	SimpleChanges         atomic.Uint64
	JointChanges          atomic.Uint64
	ConfChangesRejected   atomic.Uint64 // retried copies a replica did not apply
	ReplicasAdded         atomic.Uint64
	ReplicasRemoved       atomic.Uint64
	Partitions            atomic.Uint64
	Transfers             atomic.Uint64
	Dropped               atomic.Uint64
	Retries               atomic.Uint64
}

func (s *Stats) add(c *atomic.Uint64) { c.Add(1) }

func (s *Stats) String() string {
	return fmt.Sprintf("snapshots taken %d, sent %d, installed %d (%d at a changed configuration); "+
		"conf changes simple %d, joint %d, duplicates rejected %d; replicas added %d, removed %d; "+
		"partitions %d, leadership transfers %d, messages dropped %d, client retries %d",
		s.SnapshotsTaken.Load(), s.SnapshotsSent.Load(), s.SnapshotsInstalled.Load(), s.SnapshotsReconfigured.Load(),
		s.SimpleChanges.Load(), s.JointChanges.Load(), s.ConfChangesRejected.Load(),
		s.ReplicasAdded.Load(), s.ReplicasRemoved.Load(),
		s.Partitions.Load(), s.Transfers.Load(), s.Dropped.Load(), s.Retries.Load())
}

// initialVoters is the bootstrap configuration of every cluster.
var initialVoters = []uint64{1, 2, 3}

// sameIDs says whether a and b hold the same ids, in any order.
func sameIDs(a, b []uint64) bool {
	if len(a) != len(b) {
		return false
	}
	for _, x := range a {
		if !hasID(b, x) {
			return false
		}
	}
	return true
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

// Options are a cluster's faults and raft's optional features.
type Options struct {
	DropOneIn   uint64 // drop one message in DropOneIn at random (0: none)
	PreVote     bool
	CheckQuorum bool
}

// Cluster is a cluster of replicas connected in process: the running replicas (by id), the
// members as of the last configuration change the cluster made (its voters and learners; the
// replicas clients go to), the replicas cut off from the network, the next fresh id, the next
// operation id and configuration-change sequence number, and the statistics.
type Cluster struct {
	opts  Options
	Stats Stats

	mu       sync.Mutex
	replicas map[uint64]*Replica
	members  []uint64
	cut      map[uint64]bool
	nextID   uint64
	nextOp   uint64
	confSeq  uint64
}

// StartCluster bootstraps a cluster of initialVoters (raft.StartNode with them as the peers:
// each node's log starts with their configuration changes).
func StartCluster(opts Options) *Cluster {
	c := &Cluster{opts: opts, replicas: make(map[uint64]*Replica), cut: make(map[uint64]bool),
		members: append([]uint64(nil), initialVoters...), nextID: uint64(len(initialVoters)) + 1}
	var peers []raft.Peer
	for _, id := range initialVoters {
		peers = append(peers, raft.Peer{ID: id})
	}
	c.mu.Lock()
	for _, id := range initialVoters {
		st := raft.NewMemoryStorage()
		c.replicas[id] = newReplica(id, raft.StartNode(c.config(id, st), peers), st, &c.Stats, c.sender(id))
	}
	c.mu.Unlock()
	return c
}

// config is raft's configuration of node id on storage st.
func (c *Cluster) config(id uint64, st *raft.MemoryStorage) *raft.Config {
	return &raft.Config{
		ID:                id,
		ElectionTick:      10,
		HeartbeatTick:     1,
		Storage:           st,
		MaxSizePerMsg:     4 << 10,
		MaxInflightMsgs:   64,
		Logger:            quietLogger{},
		PreVote:           c.opts.PreVote,
		CheckQuorum:       c.opts.CheckQuorum,
		StepDownOnRemoval: true,
	}
}

// startNew starts a replica of a fresh id that is in no configuration yet (raft.RestartNode on
// an empty storage: it waits for a leader to send it the log or a snapshot), and returns its id.
func (c *Cluster) startNew() uint64 {
	c.mu.Lock()
	id := c.nextID
	c.nextID++
	st := raft.NewMemoryStorage()
	c.replicas[id] = newReplica(id, raft.RestartNode(c.config(id, st)), st, &c.Stats, c.sender(id))
	c.mu.Unlock()
	c.Stats.add(&c.Stats.ReplicasAdded)
	return id
}

// setMembers records the configuration the cluster's last change reached (not joint), and
// stops for good every running replica outside it.
func (c *Cluster) setMembers(cs *pb.ConfState) {
	members := append(append([]uint64(nil), cs.GetVoters()...), cs.GetLearners()...)
	var gone []*Replica
	c.mu.Lock()
	c.members = members
	for id, r := range c.replicas {
		if !hasID(members, id) {
			delete(c.replicas, id)
			delete(c.cut, id)
			gone = append(gone, r)
		}
	}
	c.mu.Unlock()
	for _, r := range gone {
		r.stop()
		c.Stats.add(&c.Stats.ReplicasRemoved)
	}
}

// randomMember is a random running member, or nil if there is none.
func (c *Cluster) randomMember() *Replica {
	c.mu.Lock()
	defer c.mu.Unlock()
	var rs []*Replica
	for _, id := range c.members {
		if r, ok := c.replicas[id]; ok {
			rs = append(rs, r)
		}
	}
	if len(rs) == 0 {
		return nil
	}
	return rs[primitive.RandomUint64()%uint64(len(rs))]
}

// running is the running replicas.
func (c *Cluster) running() []*Replica {
	c.mu.Lock()
	defer c.mu.Unlock()
	var rs []*Replica
	for _, r := range c.replicas {
		rs = append(rs, r)
	}
	return rs
}

// leader is the running replica that believes it is the leader of the highest term, or nil.
func (c *Cluster) leader() *Replica {
	var best *Replica
	var term uint64
	for _, r := range c.running() {
		st := r.node.Status()
		if st.RaftState == raft.StateLeader && st.HardState.GetTerm() >= term {
			best, term = r, st.HardState.GetTerm()
		}
	}
	return best
}

// sender is the transport of replica from's messages.
func (c *Cluster) sender(from uint64) func([]*pb.Message) {
	return func(ms []*pb.Message) { c.send(from, ms) }
}

// send delivers the messages of replica from to their targets, each as a fresh copy (the
// wire's), but drops those to a replica not running, from or to a replica cut off, and one in
// DropOneIn at random; the sender's node is told of a drop (Node.ReportUnreachable) and of each
// snapshot's fate (Node.ReportSnapshot: a leader waits for it before it sends the follower
// anything else). A message the target does not take within stepTimeout is dropped too: Step
// of a forwarded proposal (MsgProp) blocks while the target knows no leader, and the sender's
// loop must not wait for that (a candidate whose loop is blocked never handles the Ready that
// persists its vote, so never receives it, and a cluster whose only voter it is never elects
// anyone).
func (c *Cluster) send(from uint64, ms []*pb.Message) {
	for _, m := range ms {
		c.mu.Lock()
		src := c.replicas[from]
		dst, ok := c.replicas[m.GetTo()]
		drop := !ok || c.cut[from] || c.cut[m.GetTo()] ||
			(c.opts.DropOneIn != 0 && primitive.RandomUint64()%c.opts.DropOneIn == 0)
		c.mu.Unlock()
		if src == nil {
			return
		}
		snap := m.GetType() == pb.MsgSnap
		if drop {
			c.Stats.add(&c.Stats.Dropped)
			src.node.ReportUnreachable(m.GetTo())
			if snap {
				src.node.ReportSnapshot(m.GetTo(), raft.SnapshotFailure)
			}
			continue
		}
		ctx, cancel := context.WithTimeout(context.Background(), stepTimeout)
		err := dst.node.Step(ctx, proto.Clone(m).(*pb.Message))
		cancel()
		if err == context.DeadlineExceeded {
			c.Stats.add(&c.Stats.Dropped)
			src.node.ReportUnreachable(m.GetTo())
			if snap {
				src.node.ReportSnapshot(m.GetTo(), raft.SnapshotFailure)
			}
			continue
		}
		if snap {
			c.Stats.add(&c.Stats.SnapshotsSent)
			src.node.ReportSnapshot(m.GetTo(), raft.SnapshotFinish)
		}
	}
}

// setCut cuts replica id off the network, or reconnects it.
func (c *Cluster) setCut(id uint64, cut bool) {
	c.mu.Lock()
	if cut {
		c.cut[id] = true
	} else {
		delete(c.cut, id)
	}
	c.mu.Unlock()
}

// heal reconnects every replica.
func (c *Cluster) heal() {
	c.mu.Lock()
	c.cut = make(map[uint64]bool)
	c.mu.Unlock()
}

// stepTimeout bounds how long the transport waits for a target to take a message.
const stepTimeout = 5 * time.Millisecond

// opTimeout is how long a client waits for an answer at one replica before it tries another.
const opTimeout = 200 * time.Millisecond

// do runs one operation through the log: it gives it a fresh id and proposes it at a random
// member until one answers (the same encoding each time: it takes effect once).
func (c *Cluster) do(kind byte, key, val string) string {
	c.mu.Lock()
	c.nextOp++
	op := encode(c.nextOp, kind, key, val)
	c.mu.Unlock()
	for {
		if r := c.randomMember(); r != nil {
			if v, ok := r.propose(op, opTimeout); ok {
				return v
			}
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
// answers (a read has no effect: each attempt is a fresh one).
func (c *Cluster) Read(key string) string {
	for {
		if r := c.randomMember(); r != nil {
			if v, ok := r.read(key, opTimeout); ok {
				return v
			}
		}
		c.Stats.add(&c.Stats.Retries)
	}
}

// Stop stops every replica.
func (c *Cluster) Stop() {
	for _, r := range c.running() {
		r.stop()
	}
}

// Converged waits up to timeout for the running members to agree: the same applied index
// and the same store contents. It returns an error describing the disagreement otherwise.
func (c *Cluster) Converged(timeout time.Duration) error {
	deadline := time.Now().Add(timeout)
	for {
		c.mu.Lock()
		var rs []*Replica
		for _, id := range c.members {
			if r, ok := c.replicas[id]; ok {
				rs = append(rs, r)
			}
		}
		c.mu.Unlock()
		err := agree(rs)
		if err == nil || time.Now().After(deadline) {
			return err
		}
		time.Sleep(10 * time.Millisecond)
	}
}

// agree says whether the replicas rs have the same applied index and contents.
func agree(rs []*Replica) error {
	if len(rs) == 0 {
		return fmt.Errorf("kvreconf: no running member")
	}
	kv0, i0 := rs[0].contents()
	for _, r := range rs[1:] {
		kv, i := r.contents()
		if i != i0 {
			return fmt.Errorf("kvreconf: replica %d applied %d, replica %d applied %d", rs[0].id, i0, r.id, i)
		}
		if !within(kv, kv0) || !within(kv0, kv) {
			return fmt.Errorf("kvreconf: replicas %d and %d differ at index %d: %v, %v", rs[0].id, r.id, i, kv0, kv)
		}
	}
	return nil
}
