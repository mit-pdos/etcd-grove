// Package kvcheck is kvnet's checking client: the program the top-level robustness theorem
// (notes/kvnet-robust-goal.md) runs on a machine that never crashes, beside the replicas
// (kvnet.RunNode), each on a machine of its own that may crash. Its Check is the test's driver,
// and part of what the theorem means: the theorem says it never panics, and it panics unless
// porcupine accepts the history of the operations it ran.
//
// What it runs (kvdurable's Run, over the network): 4 clients of 100 random operations
// (kvnet.Gen: Puts, Gets through the log, Reads by a read index, of the keys "a", "b", "c"),
// each retried at random replicas until one answers, with a fresh operation id (the same
// encoding at every retry, so it takes effect once) or a fresh read sequence number (at every
// attempt); one to three proposers of random configuration changes and leadership disruptions,
// through random replicas, until the clients are done. The history is traced with a counter
// clock (lintest.CounterClock) and checked by porcupine with no timeout; Check panics unless
// porcupine answers Ok. No operation ever gives up: an operation that never gets an answer keeps
// Check running (a liveness matter, not a wrong result). It does not crash replicas or touch the
// network: every fault is the environment's.
package kvcheck

import (
	"sync"
	"time"

	"github.com/anishathalye/porcupine"
	"github.com/goose-lang/primitive"
	"github.com/mit-pdos/etcd-grove/examples/lib/lintest"
	"github.com/mit-pdos/etcd-grove/examples/raft/kvnet"
	"github.com/mit-pdos/gokv/trusted_proph"
	pb "go.etcd.io/raft/v3/raftpb"
)

// The workload, Check's own (the theorem leaves it to the program).
const (
	clients      = 4
	opsPerClient = 100
	reconfPause  = 20 * time.Millisecond
	disruptPause = 50 * time.Millisecond
)

// opTimeout is how long a client waits for an answer at one replica before it tries another.
const opTimeout = 300 * time.Millisecond

// maxSeq is the largest operation id and read sequence number.
const maxSeq = ^uint64(0)

// oneIn is true with probability 1/n.
func oneIn(n uint64) bool { return primitive.RandomUint64()%n == 0 }

// below is a random number in [0, n) (0 if n is 0).
func below(n uint64) uint64 {
	if n == 0 {
		return 0
	}
	return primitive.RandomUint64() % n
}

// checker is a run's clients' shared state: the replicas' addresses (replica i at addrs[i-1]),
// the next operation id and read sequence number, and the latest configuration a replica reported.
type checker struct {
	addrs    []string
	mu       sync.Mutex
	nextOp   uint64
	nextRead uint64
	lastConf *pb.ConfState
}

// randomID is a random replica's id.
func (c *checker) randomID() uint64 {
	return 1 + below(uint64(len(c.addrs)))
}

// request sends one request to replica id (kvnet.Request).
func (c *checker) request(id uint64, kind byte, payload []byte) ([]byte, bool) {
	return kvnet.Request(c.addrs[id-1], kind, opTimeout, payload)
}

// randomMember is a random member of the latest configuration a replica reported, or, one time in
// four or if there is none, a random replica.
func (c *checker) randomMember() uint64 {
	c.mu.Lock()
	cs := c.lastConf
	c.mu.Unlock()
	members := append(append([]uint64(nil), cs.GetVoters()...), cs.GetLearners()...)
	if len(members) == 0 || oneIn(4) {
		return c.randomID()
	}
	id := members[below(uint64(len(members)))]
	if id < 1 || id > uint64(len(c.addrs)) {
		return c.randomID()
	}
	return id
}

// conf asks a random replica for its configuration, and records it (randomMember); nil if it
// does not answer, or its answer does not decode.
func (c *checker) conf() *pb.ConfState {
	b, ok := c.request(c.randomID(), kvnet.ReqStatus, nil)
	if !ok {
		return nil
	}
	s, good := kvnet.GetStatus(b)
	if !good {
		return nil
	}
	c.mu.Lock()
	c.lastConf = s.Conf
	c.mu.Unlock()
	return s.Conf
}

// fresh is a fresh number from *next (an operation id or a read sequence number); it never
// returns once all are used (2^64 - 1 of them: it does not happen), so none is ever reused.
func (c *checker) fresh(next *uint64) uint64 {
	c.mu.Lock()
	if *next == maxSeq {
		c.mu.Unlock()
		for {
		}
	}
	*next++
	n := *next
	c.mu.Unlock()
	return n
}

// do runs one operation through the log: it gives it a fresh id and proposes it at a random
// member until one answers (the same encoding each time: it takes effect once).
func (c *checker) do(kind byte, key, val string) string {
	op := kvnet.EncodeOp(c.fresh(&c.nextOp), kind, key, val)
	for {
		if v, ok := c.request(c.randomMember(), kvnet.ReqPropose, op); ok {
			return string(v)
		}
	}
}

// read returns key's value by a read index at a random member, retried (each attempt a fresh
// read) until one answers. The prophecy p, resolved with the answer, is for the proof only, as in
// kvdurable's Cluster.Read (examples/raft/kvdurable/cluster.go): it tells the proof of read
// (KvNet/Proof/.../kvnet/kvcheck/checker__read.lean), at each change of the store, whether the
// key's value then is the answer (the read's linearization point). It has no effect.
func (c *checker) read(key string) string {
	p := primitive.NewProph()
	for {
		req := kvnet.EncodeRead(c.fresh(&c.nextRead), key)
		if v, ok := c.request(c.randomMember(), kvnet.ReqRead, req); ok {
			trusted_proph.ResolveBytes(p, v)
			return string(v)
		}
	}
}

// sleep waits a random time below 2*pause, or until stop; it says whether to stop.
func sleep(pause time.Duration, stop <-chan struct{}) bool {
	select {
	case <-stop:
		return true
	case <-time.After(time.Duration(below(uint64(2 * pause)))):
		return false
	}
}

// changeID is the id a random change names: one of the configuration's, or another replica's.
func (c *checker) changeID(cs *pb.ConfState) uint64 {
	ids := append(append(append([]uint64(nil), cs.GetVoters()...), cs.GetVotersOutgoing()...), cs.GetLearners()...)
	if len(ids) == 0 || oneIn(4) {
		return c.randomID()
	}
	return ids[below(uint64(len(ids)))]
}

// randomChange is a random configuration change, as kvdurable's: the leaving of a joint
// configuration (one time in eight), or one to three single changes of random ids and a random
// transition, as a ConfChangeV2, or, for one change of the automatic transition, one time in two
// as a ConfChange.
func (c *checker) randomChange(cs *pb.ConfState) pb.ConfChangeI {
	if oneIn(8) {
		return &pb.ConfChangeV2{}
	}
	count := 1
	if oneIn(2) {
		count = 1 + int(below(3))
	}
	var changes []*pb.ConfChangeSingle
	for i := 0; i < count; i++ {
		var t pb.ConfChangeType
		switch below(16) {
		case 0, 1, 2, 3, 4:
			t = pb.ConfChangeAddNode
		case 5, 6, 7, 8:
			t = pb.ConfChangeAddLearnerNode
		case 9, 10, 11, 12, 13, 14:
			t = pb.ConfChangeRemoveNode
		default:
			t = pb.ConfChangeUpdateNode
		}
		id := c.changeID(cs)
		changes = append(changes, &pb.ConfChangeSingle{Type: t.Enum(), NodeId: new(id)})
	}
	transition := []pb.ConfChangeTransition{pb.ConfChangeTransitionAuto,
		pb.ConfChangeTransitionJointImplicit, pb.ConfChangeTransitionJointExplicit}[below(3)]
	if count == 1 && transition == pb.ConfChangeTransitionAuto && oneIn(2) {
		return &pb.ConfChange{Type: changes[0].Type, NodeId: changes[0].NodeId}
	}
	return &pb.ConfChangeV2{Transition: transition.Enum(), Changes: changes}
}

// reconfigure proposes random configuration changes through random replicas, at random times,
// until stop, never waiting for one to be committed (as kvdurable's).
func (c *checker) reconfigure(stop <-chan struct{}) {
	for !sleep(reconfPause, stop) {
		cc := c.randomChange(c.conf())
		c.request(c.randomID(), kvnet.ReqConf, kvnet.PutConfChange(nil, cc))
	}
}

// disrupt moves leadership at random times until stop: a transfer to a random replica, a
// campaign, or a leader forgotten, asked of a random replica; or, one time in eight, a replica's
// restart in its process (its node stopped, raft's Node.Stop, and restarted from its file).
func (c *checker) disrupt(stop <-chan struct{}) {
	for !sleep(disruptPause, stop) {
		what := below(3)
		if oneIn(8) {
			what = 3
		}
		c.request(c.randomID(), kvnet.ReqDisrupt, kvnet.EncodeDisrupt(what, c.randomID()))
	}
}

// Check is the checking client's process, as the top-level theorem runs it: the cluster whose
// replicas' addresses are addrs (comma-separated, replica i at the i-th, ids from 1), with the
// bootstrap voters 1..voters. It panics if the cluster is not one the theorem's premises allow
// (kvnet.ValidAddrs), and unless porcupine accepts the history of the operations it ran (the
// package's comment); otherwise it returns once they are done.
func Check(addrs string, voters uint64) {
	as := kvnet.SplitAddrs(addrs)
	if !kvnet.ValidAddrs(as, voters) {
		panic("kvcheck: not a valid cluster")
	}
	c := &checker{addrs: as}
	stop := make(chan struct{})
	var wg sync.WaitGroup
	proposers := 1 + int(below(3))
	for i := 0; i < proposers; i++ {
		wg.Add(1)
		go func() {
			c.reconfigure(stop)
			wg.Done()
		}()
	}
	wg.Add(1)
	go func() {
		c.disrupt(stop)
		wg.Done()
	}()
	apply := func(input any) any {
		in := input.(kvnet.Input)
		if in.Kind == kvnet.OpPut {
			c.do(kvnet.OpPut, in.Key, in.Val)
			return ""
		}
		if in.Kind == kvnet.OpGet {
			return c.do(kvnet.OpGet, in.Key, "")
		}
		return c.read(in.Key)
	}
	res := lintest.Run(kvnet.Model(), apply, kvnet.Gen, lintest.CounterClock(), clients, opsPerClient, 0)
	close(stop)
	wg.Wait()
	if res != porcupine.Ok {
		panic("kvcheck: porcupine rejected the store's history")
	}
}
