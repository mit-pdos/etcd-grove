package epaxos

// An in-memory cluster of EPaxos replicas for deterministic scenario tests: the replicas are
// built without New (no network, no run loop, no executor goroutine), each replica writes to
// its peers through bufio.Writers over bytes.Buffers, and the test decodes what each replica
// sent and delivers the messages it chooses, in the order it chooses, by calling the handlers.

import (
	"bufio"
	"bytes"
	"fmt"
	"sync"
	"testing"

	"github.com/imdea-software/swiftpaxos-epaxos/dlog"
	"github.com/imdea-software/swiftpaxos-epaxos/replica"
	"github.com/imdea-software/swiftpaxos-epaxos/replica/defs"
	fastrpc "github.com/imdea-software/swiftpaxos-epaxos/rpc"
	"github.com/imdea-software/swiftpaxos-epaxos/state"
)

// testRowSize is the length of each row of InstanceSpace in a test replica (New allocates
// MAX_INSTANCE entries per row; the scenarios use a few instances).
const testRowSize = 64

type tmsg struct {
	from, to int32
	msg      fastrpc.Serializable
}

func (m *tmsg) kind() string {
	switch m.msg.(type) {
	case *Prepare:
		return "Prepare"
	case *PrepareReply:
		return "PrepareReply"
	case *PreAccept:
		return "PreAccept"
	case *PreAcceptReply:
		return "PreAcceptReply"
	case *Accept:
		return "Accept"
	case *AcceptReply:
		return "AcceptReply"
	case *Commit:
		return "Commit"
	case *TryPreAccept:
		return "TryPreAccept"
	case *TryPreAcceptReply:
		return "TryPreAcceptReply"
	}
	return "?"
}

// inst returns the instance a message is about.
func (m *tmsg) inst() (int32, int32) {
	switch x := m.msg.(type) {
	case *Prepare:
		return x.Replica, x.Instance
	case *PrepareReply:
		return x.Replica, x.Instance
	case *PreAccept:
		return x.Replica, x.Instance
	case *PreAcceptReply:
		return x.Replica, x.Instance
	case *Accept:
		return x.Replica, x.Instance
	case *AcceptReply:
		return x.Replica, x.Instance
	case *Commit:
		return x.Replica, x.Instance
	case *TryPreAccept:
		return x.Replica, x.Instance
	case *TryPreAcceptReply:
		return x.Replica, x.Instance
	}
	return -1, -1
}

func (m *tmsg) String() string {
	q, i := m.inst()
	return fmt.Sprintf("%s %d->%d (%d.%d)", m.kind(), m.from, m.to, q, i)
}

type tcluster struct {
	t       *testing.T
	n       int
	r       []*Replica
	out     [][]*bytes.Buffer // out[i][q]: bytes replica i sent to replica q
	pending []*tmsg
	replies []*bytes.Buffer // client reply buffers, one per proposal
}

// newTestReplica builds replica id of n (f failures) as New does, less the run loop, the
// executor and the network: its writer to peer q writes to out[q].
func newTestReplica(id int32, n, f int, out []*bytes.Buffer) *Replica {
	rr := &replica.Replica{
		Logger:             &dlog.Logger{},
		N:                  n,
		F:                  f,
		Id:                 id,
		PeerAddrList:       make([]string, n),
		PeerWriters:        make([]*bufio.Writer, n),
		ClientWriters:      make(map[int32]*bufio.Writer),
		Alive:              make([]bool, n),
		PreferredPeerOrder: make([]int32, n),
		State:              state.InitState(),
		RPC:                fastrpc.NewTableId(defs.RPC_TABLE),
		Stats:              &defs.Stats{M: make(map[string]int)},
		ProposeChan:        make(chan *defs.GPropose, 100),
		BeaconChan:         make(chan *defs.GBeacon, 100),
		Thrifty:            true,
		Exec:               true,
		Dreply:             true,
		Ewma:               make([]float64, n),
		Latencies:          make([]int64, n),
	}
	for q := 0; q < n; q++ {
		rr.PreferredPeerOrder[q] = int32((int(id) + 1 + q) % n)
		if int32(q) != id {
			rr.PeerWriters[q] = bufio.NewWriter(out[q])
			rr.Alive[q] = true
		}
	}
	r := &Replica{
		Replica:               rr,
		prepareChan:           make(chan fastrpc.Serializable, 100),
		preAcceptChan:         make(chan fastrpc.Serializable, 100),
		acceptChan:            make(chan fastrpc.Serializable, 100),
		commitChan:            make(chan fastrpc.Serializable, 100),
		prepareReplyChan:      make(chan fastrpc.Serializable, 100),
		preAcceptReplyChan:    make(chan fastrpc.Serializable, 100),
		preAcceptOKChan:       make(chan fastrpc.Serializable, 100),
		acceptReplyChan:       make(chan fastrpc.Serializable, 100),
		tryPreAcceptChan:      make(chan fastrpc.Serializable, 100),
		tryPreAcceptReplyChan: make(chan fastrpc.Serializable, 100),
		InstanceSpace:         make([][]*Instance, n),
		crtInstance:           make([]int32, n),
		CommittedUpTo:         make([]int32, n),
		ExecedUpTo:            make([]int32, n),
		conflicts:             make([]map[state.Key]*InstPair, n),
		lastScan:              make([]int32, n),
		lastPut:               make([]int32, n),
		maxSeqPerKey:          make(map[state.Key]int32),
		latestCPReplica:       0,
		latestCPInstance:      -1,
		clientMutex:           new(sync.Mutex),
		instancesToRecover:    make(chan *instanceId, 100),
		maxRecvBallot:         -1,
	}
	for q := 0; q < n; q++ {
		r.InstanceSpace[q] = make([]*Instance, testRowSize)
		r.crtInstance[q] = -1
		r.ExecedUpTo[q] = -1
		r.CommittedUpTo[q] = -1
		r.conflicts[q] = make(map[state.Key]*InstPair)
		r.lastScan[q] = -1
		r.lastPut[q] = -1
	}
	r.exec = &Exec{r: r, stack: make([]*Instance, 0, 100)}
	r.prepareRPC = r.RPC.Register(new(Prepare), r.prepareChan)
	r.prepareReplyRPC = r.RPC.Register(new(PrepareReply), r.prepareReplyChan)
	r.preAcceptRPC = r.RPC.Register(new(PreAccept), r.preAcceptChan)
	r.preAcceptReplyRPC = r.RPC.Register(new(PreAcceptReply), r.preAcceptReplyChan)
	r.acceptRPC = r.RPC.Register(new(Accept), r.acceptChan)
	r.acceptReplyRPC = r.RPC.Register(new(AcceptReply), r.acceptReplyChan)
	r.commitRPC = r.RPC.Register(new(Commit), r.commitChan)
	r.tryPreAcceptRPC = r.RPC.Register(new(TryPreAccept), r.tryPreAcceptChan)
	r.tryPreAcceptReplyRPC = r.RPC.Register(new(TryPreAcceptReply), r.tryPreAcceptReplyChan)
	return r
}

// newCluster builds n replicas (f = (n-1)/2), as the deployment does: thrifty, execution on,
// replies after execution.
func newCluster(t *testing.T, n int) *tcluster {
	c := &tcluster{t: t, n: n}
	c.out = make([][]*bytes.Buffer, n)
	for i := 0; i < n; i++ {
		c.out[i] = make([]*bytes.Buffer, n)
		for q := 0; q < n; q++ {
			c.out[i][q] = new(bytes.Buffer)
		}
	}
	for i := 0; i < n; i++ {
		c.r = append(c.r, newTestReplica(int32(i), n, (n-1)/2, c.out[i]))
	}
	return c
}

// collect decodes every message the replicas have sent since the last call and appends it to
// the pending messages, in the order each replica sent them.
func (c *tcluster) collect() {
	for i := 0; i < c.n; i++ {
		for q := 0; q < c.n; q++ {
			buf := c.out[i][q]
			for buf.Len() > 0 {
				code, _ := buf.ReadByte()
				p, ok := c.r[q].RPC.Get(code)
				if !ok {
					c.t.Fatalf("unknown message code %d from %d to %d", code, i, q)
				}
				m := p.Obj.New()
				if err := m.Unmarshal(buf); err != nil {
					c.t.Fatalf("cannot decode a message from %d to %d: %v", i, q, err)
				}
				c.pending = append(c.pending, &tmsg{int32(i), int32(q), m})
			}
		}
	}
}

// deliver hands m to its destination's handler, as the run loop does.
func (c *tcluster) deliver(m *tmsg) {
	r := c.r[m.to]
	switch x := m.msg.(type) {
	case *Prepare:
		r.handlePrepare(x)
	case *PrepareReply:
		r.handlePrepareReply(x)
	case *PreAccept:
		r.handlePreAccept(x)
	case *PreAcceptReply:
		r.handlePreAcceptReply(x)
	case *Accept:
		r.handleAccept(x)
	case *AcceptReply:
		r.handleAcceptReply(x)
	case *Commit:
		r.handleCommit(x)
	case *TryPreAccept:
		r.handleTryPreAccept(x)
	case *TryPreAcceptReply:
		r.handleTryPreAcceptReply(x)
	}
	c.collect()
}

type filter func(*tmsg) bool

func kind(k string) filter { return func(m *tmsg) bool { return m.kind() == k } }
func from(i int32) filter  { return func(m *tmsg) bool { return m.from == i } }
func to(i int32) filter    { return func(m *tmsg) bool { return m.to == i } }
func toAny(is ...int32) filter {
	return func(m *tmsg) bool {
		for _, i := range is {
			if m.to == i {
				return true
			}
		}
		return false
	}
}
func instOf(q, i int32) filter {
	return func(m *tmsg) bool { a, b := m.inst(); return a == q && b == i }
}

func all(fs ...filter) filter {
	return func(m *tmsg) bool {
		for _, f := range fs {
			if !f(m) {
				return false
			}
		}
		return true
	}
}

// take removes the pending messages matching every filter and returns them, oldest first.
func (c *tcluster) take(fs ...filter) []*tmsg {
	c.collect()
	f := all(fs...)
	var got, rest []*tmsg
	for _, m := range c.pending {
		if f(m) {
			got = append(got, m)
		} else {
			rest = append(rest, m)
		}
	}
	c.pending = rest
	return got
}

// run delivers the pending messages matching the filters, oldest first (the messages they cause
// are not delivered), and returns how many it delivered.
func (c *tcluster) run(fs ...filter) int {
	ms := c.take(fs...)
	for _, m := range ms {
		c.deliver(m)
	}
	return len(ms)
}

// drop loses the pending messages matching the filters.
func (c *tcluster) drop(fs ...filter) int { return len(c.take(fs...)) }

// count returns the number of pending messages matching the filters.
func (c *tcluster) count(fs ...filter) int {
	c.collect()
	f := all(fs...)
	k := 0
	for _, m := range c.pending {
		if f(m) {
			k++
		}
	}
	return k
}

func put(k int64, v string) state.Command {
	return state.Command{Op: state.PUT, K: state.Key(k), V: state.Value(v)}
}

func get(k int64) state.Command {
	return state.Command{Op: state.GET, K: state.Key(k), V: state.NIL()}
}

// propose has replica i's run loop take one batch of client proposals (handlePropose with the
// rest of the batch pending in ProposeChan); each proposal's reply goes to its own buffer.
func (c *tcluster) propose(i int32, cmds ...state.Command) {
	r := c.r[i]
	var ps []*defs.GPropose
	for k, cmd := range cmds {
		buf := new(bytes.Buffer)
		c.replies = append(c.replies, buf)
		ps = append(ps, &defs.GPropose{
			Propose: &defs.Propose{CommandId: int32(len(c.replies)), ClientId: int32(k), Command: cmd},
			Reply:   bufio.NewWriter(buf),
			Mutex:   new(sync.Mutex),
		})
	}
	for _, p := range ps[1:] {
		r.ProposeChan <- p
	}
	r.handlePropose(ps[0])
	c.collect()
}

// recover has replica i's run loop start the recovery of instance q.k (what the executor asks
// for through instancesToRecover).
func (c *tcluster) recover(i, q, k int32) {
	c.r[i].startRecoveryForInstance(q, k)
	c.collect()
}

func (c *tcluster) inst(i, q, k int32) *Instance { return c.r[i].InstanceSpace[q][k] }

func committed(in *Instance) bool { return in != nil && in.Status >= COMMITTED }

func sameCmds(a, b []state.Command) bool {
	if len(a) != len(b) {
		return false
	}
	for i := range a {
		if a[i].Op != b[i].Op || a[i].K != b[i].K || !bytes.Equal(a[i].V, b[i].V) {
			return false
		}
	}
	return true
}

func cmdsString(cs []state.Command) string {
	s := "["
	for i := range cs {
		s += cs[i].String() + " "
	}
	return s + "]"
}

func instString(in *Instance) string {
	return fmt.Sprintf("{cmds %s seq %d deps %v status %d bal %d vbal %d}", cmdsString(in.Cmds), in.Seq, in.Deps, in.Status, in.bal, in.vbal)
}

// agreementError returns a description of the first instance two replicas have committed with
// different values (commands, seq, deps), or "".
func (c *tcluster) agreementError() string {
	for q := int32(0); q < int32(c.n); q++ {
		for k := int32(0); k < testRowSize; k++ {
			var first *Instance
			var fi int
			for i := 0; i < c.n; i++ {
				in := c.r[i].InstanceSpace[q][k]
				if !committed(in) {
					continue
				}
				if first == nil {
					first, fi = in, i
					continue
				}
				if !sameCmds(first.Cmds, in.Cmds) || first.Seq != in.Seq || !equal(first.Deps, in.Deps) {
					return fmt.Sprintf("instance %d.%d: replica %d committed %s, replica %d committed %s",
						q, k, fi, instString(first), i, instString(in))
				}
			}
		}
	}
	return ""
}

func realConflict(a, b []state.Command) bool {
	for i := range a {
		for j := range b {
			if a[i].Op == state.NONE || b[j].Op == state.NONE {
				continue
			}
			if state.Conflict(&a[i], &b[j]) {
				return true
			}
		}
	}
	return false
}

// depsError checks the dependency invariant over the instances committed at some replica: for
// two interfering committed instances, one has the other in its deps (deps[q] = d covers every
// instance of row q up to d). It returns a description of a violation, or "".
func (c *tcluster) depsError() string {
	type ci struct {
		q, k int32
		in   *Instance
	}
	var cs []ci
	for q := int32(0); q < int32(c.n); q++ {
		for k := int32(0); k < testRowSize; k++ {
			for i := 0; i < c.n; i++ {
				if in := c.r[i].InstanceSpace[q][k]; committed(in) {
					cs = append(cs, ci{q, k, in})
					break
				}
			}
		}
	}
	for x := range cs {
		for y := x + 1; y < len(cs); y++ {
			a, b := cs[x], cs[y]
			if !realConflict(a.in.Cmds, b.in.Cmds) {
				continue
			}
			if a.in.Deps[b.q] >= b.k || b.in.Deps[a.q] >= a.k {
				continue
			}
			return fmt.Sprintf("interfering committed instances %d.%d %s and %d.%d %s: neither is in the other's deps",
				a.q, a.k, instString(a.in), b.q, b.k, instString(b.in))
		}
	}
	return ""
}

// execAll runs replica i's executor on its committed instances until nothing more executes
// (executeCommand, as each scan of executeCommands does).
func (c *tcluster) execAll(i int32) {
	r := c.r[i]
	for progress := true; progress; {
		progress = false
		for q := int32(0); q < int32(c.n); q++ {
			for k := r.ExecedUpTo[q] + 1; k <= r.crtInstance[q]; k++ {
				in := r.InstanceSpace[q][k]
				if in == nil || in.Status < COMMITTED || in.Cmds == nil {
					break
				}
				if in.Status == EXECUTED {
					if k == r.ExecedUpTo[q]+1 {
						r.ExecedUpTo[q] = k
					}
					continue
				}
				if r.exec.executeCommand(q, k) {
					progress = true
					if k == r.ExecedUpTo[q]+1 {
						r.ExecedUpTo[q] = k
					}
				}
			}
		}
	}
}

// value returns the value of key k in replica i's store ("" if absent).
func (c *tcluster) value(i int32, k int64) string {
	cmd := get(k)
	return string(cmd.Execute(c.r[i].State))
}

// TestClusterFaultFree checks the helper on a fault-free schedule: one command, every message
// delivered, every replica commits and executes it, and the client gets its reply.
func TestClusterFaultFree(t *testing.T) {
	c := newCluster(t, 5)
	c.propose(0, put(1, "a"))
	for c.run() > 0 {
	}
	for i := int32(0); i < 5; i++ {
		if !committed(c.inst(i, 0, 0)) {
			continue
		}
		c.execAll(i)
		if v := c.value(i, 1); v != "a" {
			t.Fatalf("replica %d: key 1 is %q", i, v)
		}
	}
	if !committed(c.inst(0, 0, 0)) {
		t.Fatalf("the leader did not commit")
	}
	if c.replies[0].Len() == 0 {
		t.Fatalf("no reply to the client")
	}
	if e := c.agreementError(); e != "" {
		t.Fatal(e)
	}
}

// settle delivers the pending messages matching the filters, and the ones they cause, until none
// is left.
func (c *tcluster) settle(fs ...filter) {
	for c.run(fs...) > 0 {
	}
}

func not(f filter) filter { return func(m *tmsg) bool { return !f(m) } }

func fromAny(is ...int32) filter {
	return func(m *tmsg) bool {
		for _, i := range is {
			if m.from == i {
				return true
			}
		}
		return false
	}
}

// among: messages between replicas of the set.
func among(is ...int32) filter { return all(fromAny(is...), toAny(is...)) }
