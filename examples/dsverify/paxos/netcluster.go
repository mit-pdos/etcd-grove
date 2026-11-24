package paxos

import (
	"sync"
	"time"
)

// A deployment over TCP (tcpnet.go), one process per node. Node addresses are
// addrs[0..]: addrs[i-1] runs acceptor i (1 <= i <= nA, one per node),
// addrs[nA+j] runs learner 2001+j (0 <= j < nL), and addrs[nA+nL+c] is client
// c's node (0 <= c < nC), which hosts c's two agents: its proposer 1001+c and
// its box 3001+c, where learners report what they learned. Every acceptor sends
// what it accepts to every learner. Bounds as paxos-m0's NewCluster: nA, nL,
// nC <= 1000 (agent ids distinct; proposer ids below 1<<16, as proposal
// numbers need), and 1 <= nA.
//
// (etcd-grove, notes/dsv-paxos.md: dsverify-lab's paxos-net-3 kept the nC
// clients together on one client node, addrs[0]; here each client is a machine
// of its own, examples/lib/remote's design, so client c's agents are at its own
// address.)

// Learned is the type of a learner's report to a client's box: the value it
// learned (in value).
const Learned msgType = 5

// AnnounceMs is how often a learner reports its latest learned value to every
// client's box; a new value is reported within TickMs.
const AnnounceMs uint64 = 200

// TickMs is the step of a learner's reporter.
const TickMs uint64 = 5

// PollMs is the step of a client's wait for a report.
const PollMs uint64 = 100

func netProposerId(c uint64) int { return 1001 + int(c) }
func netLearnerId(j uint64) int  { return 2001 + int(j) }
func netBoxId(c uint64) int      { return 3001 + int(c) }

// agentAddrs maps every agent of the deployment to its node's address.
func agentAddrs(addrs []string, nA uint64, nL uint64, nC uint64) map[int]string {
	m := make(map[int]string)
	for i := uint64(1); i <= nA; i++ {
		m[int(i)] = addrs[i-1]
	}
	for j := uint64(0); j < nL; j++ {
		m[netLearnerId(j)] = addrs[nA+j]
	}
	for c := uint64(0); c < nC; c++ {
		m[netProposerId(c)] = addrs[nA+nL+c]
		m[netBoxId(c)] = addrs[nA+nL+c]
	}
	return m
}

func acceptorIds(nA uint64) []int {
	ids := make([]int, 0, nA)
	for i := uint64(1); i <= nA; i++ {
		ids = append(ids, int(i))
	}
	return ids
}

func learnerIds(nL uint64) []int {
	ids := make([]int, 0, nL)
	for j := uint64(0); j < nL; j++ {
		ids = append(ids, netLearnerId(j))
	}
	return ids
}

// RunServer runs server node me (1 <= me <= nA+nL) of the deployment: it
// listens on addrs[me-1] (retrying until it can) and runs its acceptor or
// learner. It never returns.
func RunServer(addrs []string, me uint64, nA uint64, nL uint64, nC uint64) {
	all := agentAddrs(addrs, nA, nL, nC)
	if me <= nA {
		id := int(me)
		nd := newTCPNode(all, []int{id})
		for !nd.serve(addrs[me-1], 10) {
		}
		a := newAcceptor(id, nd.network(id), learnerIds(nL)...)
		a.run()
	}
	if nA < me && me <= nA+nL {
		id := netLearnerId(me - nA - 1)
		nd := newTCPNode(all, []int{id})
		for !nd.serve(addrs[me-1], 10) {
		}
		runLearner(newLearner(id, nd.network(id), acceptorIds(nA)...), nd.network(id), nC)
	}
	for {
		time.Sleep(time.Hour)
	}
}

// decision is a learner's latest learned value, if any, and how many times it
// changed.
type decision struct {
	mu      *sync.Mutex
	value   string
	known   bool
	changes uint64
}

func (d *decision) set(v string) {
	d.mu.Lock()
	if !d.known || d.value != v {
		d.changes++
	}
	d.value = v
	d.known = true
	d.mu.Unlock()
}

func (d *decision) get() (string, bool, uint64) {
	d.mu.Lock()
	v := d.value
	k := d.known
	n := d.changes
	d.mu.Unlock()
	return v, k, n
}

// runLearner runs learner l forever: each time l learns a chosen value (again,
// as accepts arrive) it records it; a second goroutine reports the latest one to
// every client's box when it changes and every AnnounceMs, over nt (l's network: l only receives,
// the reporter only sends). Never returns.
func runLearner(l *learner, nt *tcpNetwork, nC uint64) {
	d := &decision{mu: new(sync.Mutex)}
	go announce(nt, d, nC)
	for {
		v := l.learn()
		d.set(v)
	}
}

// announce reports d's value, once known, to every client's box when it
// changes (checked every TickMs) and every AnnounceMs, forever.
func announce(nt *tcpNetwork, d *decision, nC uint64) {
	sent := uint64(0)
	ticks := uint64(0)
	for {
		v, known, changes := d.get()
		if known && (changes != sent || ticks >= AnnounceMs/TickMs) {
			for c := uint64(0); c < nC; c++ {
				nt.send(message{from: nt.me, to: netBoxId(c), typ: Learned, value: v})
			}
			sent = changes
			ticks = 0
		}
		time.Sleep(time.Duration(TickMs) * time.Millisecond)
		ticks++
	}
}

// NetCluster is a client's node of a deployment: the client's proposer and
// box, and whether it has proposed.
type NetCluster struct {
	node      *tcpNode
	acceptors []int
	mu        *sync.Mutex
	used      []bool
}

// NewNetCluster makes client me's node of a deployment with nA acceptors, nL
// learners and nC clients over the node addresses addrs (see above), and
// listens on addrs[nA+nL+me] (trying for 5 s; without a listener no reply
// arrives and every Propose ends with an unknown outcome).
func NewNetCluster(addrs []string, me uint64, nA uint64, nL uint64, nC uint64) *NetCluster {
	local := []int{netProposerId(me), netBoxId(me)}
	nd := newTCPNode(agentAddrs(addrs, nA, nL, nC), local)
	nd.serve(addrs[nA+nL+me], 50)
	return &NetCluster{node: nd, acceptors: acceptorIds(nA), mu: new(sync.Mutex), used: make([]bool, nC)}
}

// Propose is client c's proposal of v (c < nC, the node's own client), the write-once register's
// operation: it starts c's proposer with v and returns the first value a
// learner reports to c's box after the call, and true. It returns ("", false),
// an unknown outcome, if no report arrives within waitMs (the proposal may
// still take effect), or with no effect if c has proposed before (a proposer id
// must not be reused, since its proposal numbers would be).
func (cl *NetCluster) Propose(c uint64, v string, waitMs uint64) (string, bool) {
	cl.mu.Lock()
	first := !cl.used[c]
	cl.used[c] = true
	cl.mu.Unlock()
	if !first {
		return "", false
	}
	box := cl.node.network(netBoxId(c))
	// reports sent before the call may carry an older decision: drop them
	for {
		_, ok := box.poll()
		if !ok {
			break
		}
	}
	p := newProposer(netProposerId(c), v, cl.node.network(netProposerId(c)), cl.acceptors...)
	go p.run()
	for i := uint64(0); i < waitMs/PollMs; i++ {
		m, ok := box.recv(time.Duration(PollMs) * time.Millisecond)
		if ok && m.typ == Learned {
			return m.value, true
		}
	}
	return "", false
}
