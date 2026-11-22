// Package paxosnet is the paxos kit (dsverify-lab's paxos-net-3, notes/dsv-paxos.md) as an
// instance of examples/lib/remote: xiang90/paxos over TCP (Go's net package), a write-once register
// whose clients each run on a machine of their own, checked by porcupine on an orchestrator machine.
// Ten machines, each a command of cmd/:
//
//   - the orchestrator (Orch): remote.Check of NC clients' proposals, one each, made at the
//     clients' own machines, against the write-once register with pending proposals (Model);
//   - client machine c (Client): remote.ServeClient whose operation is c's proposal over its own
//     paxos.NetCluster (its proposer and box, at its own paxos address);
//   - server machine id (Server, 1 <= id <= NAcceptors+NLearners): an acceptor or a learner
//     (paxos.RunServer).
//
// A proposal whose call fails, or that learns nothing in time, has an unknown outcome
// (Out{Unknown: true}): it may have taken effect, may take effect later, or never.
//
// (dsverify-lab's kit ran the NC clients on one client node with its own driver, recorder and
// write-once checker; here they are remote's, lintest's and porcupine's.)
package paxosnet

import (
	"time"

	"github.com/anishathalye/porcupine"
	"github.com/mit-pdos/etcd-grove/examples/lib/remote"
	"github.com/xiang90/paxos"
)

// The configuration: NC clients, Ops operations each, NAcceptors acceptors and NLearners learners,
// how long a proposal waits to learn its outcome, and how long clients 2 and 3 wait before they
// propose (so that their proposers find a value already accepted and must adopt it).
const (
	NC            uint64 = 4
	Ops           uint64 = 1
	NAcceptors    uint64 = 3
	NLearners     uint64 = 2
	ProposeWaitMs uint64 = 10000
	StaggerMs     uint64 = 1000
)

// AttemptMs bounds one call between the orchestrator and a client machine: a client's stagger
// and its proposal's wait, with time to spare.
const AttemptMs uint64 = 15000

// PaxosAddrs is the paxos deployment's node addresses (paxos.NewNetCluster's layout): acceptors
// 1..3, learners 2001, 2002, then client c's paxos address, c = 0..3.
func PaxosAddrs() []string {
	return []string{
		"127.0.0.1:7401",
		"127.0.0.1:7402",
		"127.0.0.1:7403",
		"127.0.0.1:7404",
		"127.0.0.1:7405",
		"127.0.0.1:7406",
		"127.0.0.1:7407",
		"127.0.0.1:7408",
		"127.0.0.1:7409",
	}
}

// ClientAddrs is the client machines' addresses for the orchestrator's calls (remote.Serve).
func ClientAddrs() []string {
	return []string{
		"127.0.0.1:7411",
		"127.0.0.1:7412",
		"127.0.0.1:7413",
		"127.0.0.1:7414",
	}
}

// Out is a proposal's output: the decided value it learned, or Unknown (its outcome is unknown).
type Out struct {
	Unknown bool
	V       string
}

// State is the model's state: whether a value is known to be decided (Known, Val), and the
// proposals of unknown outcome (Pend; each may still take effect, once, or never). With Known it
// stands for the configurations (Val decided, some of Pend still pending); without, for nothing
// decided and all of Pend pending, or one x of Pend decided and some of the others pending.
type State struct {
	Known bool
	Val   string
	Pend  []string
}

// push is p with v added, in a new slice (states are never written).
func push(p []string, v string) []string {
	q := make([]string, len(p)+1)
	copy(q, p)
	q[len(p)] = v
	return q
}

// has reports whether v is in p.
func has(p []string, v string) bool {
	for i := 0; i < len(p); i++ {
		if p[i] == v {
			return true
		}
	}
	return false
}

// erase is p without its first v, in a new slice.
func erase(p []string, v string) []string {
	q := make([]string, 0, len(p))
	found := false
	for i := 0; i < len(p); i++ {
		if !found && p[i] == v {
			found = true
		} else {
			q = append(q, p[i])
		}
	}
	return q
}

// step is the model's step: a proposal of unknown outcome is pending; an answered proposal of in
// that learned v is one at a configuration where v is decided (already, or by in itself, or by a
// pending proposal of v taking effect first).
func step(s State, in string, o Out) (bool, State) {
	if o.Unknown {
		return true, State{Known: s.Known, Val: s.Val, Pend: push(s.Pend, in)}
	}
	if s.Known {
		if o.V == s.Val {
			return true, s
		}
		return false, s
	}
	if o.V == in {
		return true, State{Known: true, Val: in, Pend: s.Pend}
	}
	if has(s.Pend, o.V) {
		return true, State{Known: true, Val: o.V, Pend: erase(s.Pend, o.V)}
	}
	return false, s
}

// equal reports whether a and b are the same state (as values: the same pending list).
func equal(a State, b State) bool {
	if a.Known != b.Known || a.Val != b.Val || len(a.Pend) != len(b.Pend) {
		return false
	}
	for i := 0; i < len(a.Pend); i++ {
		if a.Pend[i] != b.Pend[i] {
			return false
		}
	}
	return true
}

// Model is the write-once register with pending proposals (linkv's pending-writes model of the
// register: every proposal is a write), as a porcupine model. Inputs are strings, outputs Outs.
func Model() porcupine.Model {
	return porcupine.Model{
		Init: func() any { return State{} },
		Step: func(state, input, output any) (bool, any) {
			ok, s := step(state.(State), input.(string), output.(Out))
			return ok, s
		},
		Equal: func(a, b any) bool { return equal(a.(State), b.(State)) },
	}
}

// Codec is the register's codec: an input as its bytes, an output as one byte (1: unknown) and
// the value's bytes.
func Codec() remote.Codec {
	return remote.Codec{
		EncIn: func(in any) []byte {
			return []byte(in.(string))
		},
		DecIn: func(b []byte) (any, bool) {
			return string(b), true
		},
		EncOut: func(out any) []byte {
			o := out.(Out)
			b := make([]byte, 1, 1+len(o.V))
			if o.Unknown {
				b[0] = 1
			}
			return append(b, []byte(o.V)...)
		},
		DecOut: func(b []byte) (any, bool) {
			if len(b) < 1 || b[0] > 1 {
				return nil, false
			}
			return Out{Unknown: b[0] == 1, V: string(b[1:])}, true
		},
		IsRead:    func(in any) bool { return false },
		Unknown:   func(in any) any { return Out{Unknown: true} },
		IsUnknown: func(out any) bool { return out.(Out).Unknown },
	}
}

// Gen is client c's input: "v1" .. "v4".
func Gen(c int) any {
	if c == 0 {
		return "v1"
	}
	if c == 1 {
		return "v2"
	}
	if c == 2 {
		return "v3"
	}
	return "v4"
}

// attempt is AttemptMs as a duration.
func attempt() time.Duration {
	return time.Duration(AttemptMs) * time.Millisecond
}

// Orch is the orchestrator's program: it panics unless porcupine accepts the history of the
// clients' proposals.
func Orch() {
	remote.Check(Model(), ClientAddrs(), Codec(), Gen, int(Ops), attempt())
}

// Client is client machine c's program (c < NC): its own client node of the paxos deployment,
// served at its address in ClientAddrs; its operation waits (c/2)*StaggerMs, then proposes. The
// node is made once, before serving (remote.ServeClient's newClient may be called any number of
// times as far as its contract says, and a second node of client c would reuse its proposer's
// proposal numbers).
func Client(c uint64) {
	cl := paxos.NewNetCluster(PaxosAddrs(), c, NAcceptors, NLearners, NC)
	newClient := func(id int) any {
		return cl
	}
	op := func(sys any, in any) any {
		time.Sleep(time.Duration((c/2)*StaggerMs) * time.Millisecond)
		v, ok := sys.(*paxos.NetCluster).Propose(c, in.(string), ProposeWaitMs)
		if !ok {
			return Out{Unknown: true}
		}
		return Out{V: v}
	}
	remote.ServeClient(int(c), ClientAddrs()[c], newClient, op, Codec(), attempt())
}

// Server is server machine id's program (1 <= id <= NAcceptors+NLearners). It never returns.
func Server(id uint64) {
	paxos.RunServer(PaxosAddrs(), id, NAcceptors, NLearners, NC)
}
