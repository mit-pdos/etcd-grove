// Package gryffnet is the gryff kit (dsverify-lab's gryff-bump-1, notes/dsv-gryff.md) as an
// instance of examples/lib/remote: Gryff (its replicas in proxy mode, registered with Gryff's
// master over net/rpc) over TCP (Go's net package), an int64 register with compare-and-swap whose
// clients each run on a machine of their own, checked by porcupine on an orchestrator machine.
// Eleven machines, each a command of cmd/:
//
//   - the orchestrator (Orch): remote.Check of NC clients' operations, K each, made at the clients'
//     own machines, against the register with pending operations (Model);
//   - client machine c (Client): remote.ServeClient whose operation is client c's Read, Write or
//     RMW (a compare-and-swap) sent to its replica (Op), as Gryff's own client sends it in proxy
//     mode;
//   - server machine id (Server, 1 <= id <= 1+NReplicas): Gryff's master (id 1) or a replica.
//
// An operation whose call fails, or that gets no reply, has an unknown outcome (Out{Unknown:
// true}): it may have taken effect, may take effect later, or never.
//
// (dsverify-lab's kit ran each client on a node of its own with its own driver, recorder and
// checker, the lab's Remote; here they are remote's, lintest's and porcupine's, and the model's
// pending operations are kept by the model itself.)
package gryffnet

import (
	"bufio"
	"encoding/binary"
	"math/rand"
	"net"
	"net/rpc"
	"strings"
	"sync"
	"time"

	"github.com/anishathalye/porcupine"
	"github.com/mit-pdos/etcd-grove/examples/lib/remote"
	"gryff/src/clientproto"
	"gryff/src/gryff"
	"gryff/src/gryffproto"
	"gryff/src/masterlib"
	"gryff/src/serverlib"
	"gryff/src/state"
)

// The configuration (the lab's kit.toml): NC clients, K operations each, NReplicas replicas, the
// register's key, the replicas' timeouts, a client's dial limit, and the clients' start (every
// client waits StartMs for the replicas to register with the master and connect to each other;
// clients 2p and 2p+1 then start together, p * StaggerMs later).
const (
	NC              uint64 = 6
	K               uint64 = 4
	NReplicas       uint64 = 3
	Key             uint64 = 0
	ShortcircuitMs  uint64 = 100
	FastOverwriteMs uint64 = 100
	ForceWriteMs    uint64 = 100
	DialMs          uint64 = 3000
	StartMs         uint64 = 4000
	StaggerMs       uint64 = 300
)

// CallMs bounds one call between the orchestrator and a client machine (the lab's CallMs): a
// client's start and its operation, with time to spare.
const CallMs uint64 = 20000

// ServerAddrs is the server machines' addresses, server id at index id-1: the master (id 1),
// then the replicas (ids 2..1+NReplicas). A server listens on its address's port; a replica's
// net/rpc server (the master's pings) 1000 above it.
func ServerAddrs() []string {
	return []string{
		"127.0.0.1:7501",
		"127.0.0.1:7502",
		"127.0.0.1:7503",
		"127.0.0.1:7504",
	}
}

// ClientAddrs is the client machines' addresses for the orchestrator's calls (remote.Serve).
func ClientAddrs() []string {
	return []string{
		"127.0.0.1:7511",
		"127.0.0.1:7512",
		"127.0.0.1:7513",
		"127.0.0.1:7514",
		"127.0.0.1:7515",
		"127.0.0.1:7516",
	}
}

// The register's operations (In.Op).
const (
	OpRead  uint64 = 0
	OpWrite uint64 = 1
	OpCAS   uint64 = 2
)

// In is a register operation: Read; Write(A); CAS(A, B) (if the value is A, set it to B). An Op
// other than OpWrite and OpCAS is a Read; fields an operation does not use are zero.
type In struct {
	Op uint64
	A  int64
	B  int64
}

// Out is an operation's output: Unknown (its outcome is unknown), or a Read's value V; a Write's
// and a CAS's output is Out{} (Gryff's RMWReply does not say whether the swap happened: later
// reads find its effect, if any).
type Out struct {
	Unknown bool
	V       int64
}

// apply is the register's step from value v: the next value and the output.
func apply(v int64, in In) (int64, Out) {
	if in.Op == OpWrite {
		return in.A, Out{}
	}
	if in.Op == OpCAS {
		if v == in.A {
			return in.B, Out{}
		}
		return v, Out{}
	}
	return v, Out{V: v}
}

// isWrite reports whether in changes the register (a Write or a CAS): only those are left pending
// when their outcome is unknown.
func isWrite(in In) bool {
	return in.Op == OpWrite || in.Op == OpCAS
}

// Cfg is a configuration: the register's value, and the operations of unknown outcome that may
// still take effect (each at most once).
type Cfg struct {
	V    int64
	Pend []In
}

// State is the model's state: the configurations the history may have reached are those
// reachable from Cfgs by pending operations taking effect (reach).
type State struct {
	Cfgs []Cfg
}

// without is p without its element at index i, in a new slice.
func without(p []In, i int) []In {
	q := make([]In, 0, len(p))
	for j := 0; j < len(p); j++ {
		if j != i {
			q = append(q, p[j])
		}
	}
	return q
}

// with is p with x added at the end, in a new slice.
func with(p []In, x In) []In {
	q := make([]In, len(p)+1)
	copy(q, p)
	q[len(p)] = x
	return q
}

// sameCfg reports whether a and b are the same configuration (the same pending list, in order).
func sameCfg(a Cfg, b Cfg) bool {
	if a.V != b.V || len(a.Pend) != len(b.Pend) {
		return false
	}
	for i := 0; i < len(a.Pend); i++ {
		if a.Pend[i] != b.Pend[i] {
			return false
		}
	}
	return true
}

// hasCfg reports whether c is in cs.
func hasCfg(cs []Cfg, c Cfg) bool {
	for i := 0; i < len(cs); i++ {
		if sameCfg(cs[i], c) {
			return true
		}
	}
	return false
}

// reach is the configurations reachable from c by pending operations taking effect (c included).
// Each takes effect at most once, so the search ends.
func reach(c Cfg) []Cfg {
	out := []Cfg{c}
	for k := 0; k < len(out); k++ {
		x := out[k]
		for i := 0; i < len(x.Pend); i++ {
			v, _ := apply(x.V, x.Pend[i])
			y := Cfg{V: v, Pend: without(x.Pend, i)}
			if !hasCfg(out, y) {
				out = append(out, y)
			}
		}
	}
	return out
}

// step is the model's step: an operation of unknown outcome that writes is pending in every
// configuration (one that reads does nothing); an answered operation is one at a configuration
// reachable from the state's whose output is the answer.
func step(s State, in In, o Out) (bool, State) {
	if o.Unknown {
		if !isWrite(in) {
			return true, s
		}
		cs := make([]Cfg, 0, len(s.Cfgs))
		for i := 0; i < len(s.Cfgs); i++ {
			cs = append(cs, Cfg{V: s.Cfgs[i].V, Pend: with(s.Cfgs[i].Pend, in)})
		}
		return true, State{Cfgs: cs}
	}
	cs := make([]Cfg, 0)
	for i := 0; i < len(s.Cfgs); i++ {
		r := reach(s.Cfgs[i])
		for j := 0; j < len(r); j++ {
			v, want := apply(r[j].V, in)
			y := Cfg{V: v, Pend: r[j].Pend}
			if want == o && !hasCfg(cs, y) {
				cs = append(cs, y)
			}
		}
	}
	return len(cs) > 0, State{Cfgs: cs}
}

// equal reports whether a and b are the same state (as values: the same configurations, in order).
func equal(a State, b State) bool {
	if len(a.Cfgs) != len(b.Cfgs) {
		return false
	}
	for i := 0; i < len(a.Cfgs); i++ {
		if !sameCfg(a.Cfgs[i], b.Cfgs[i]) {
			return false
		}
	}
	return true
}

// Model is the int64 register from 0 whose compare-and-swap does not report its outcome, with
// pending operations (a write or compare-and-swap of unknown outcome may take effect at any later
// time, once, or never), as a porcupine model. Inputs are Ins, outputs Outs.
func Model() porcupine.Model {
	return porcupine.Model{
		Init: func() any { return State{Cfgs: []Cfg{Cfg{V: 0, Pend: nil}}} },
		Step: func(state, input, output any) (bool, any) {
			ok, s := step(state.(State), input.(In), output.(Out))
			return ok, s
		},
		Equal: func(a, b any) bool { return equal(a.(State), b.(State)) },
	}
}

// Codec is the register's codec: an input as 24 bytes (Op, A, B), an output as 9 (1 if unknown,
// else 0; V), each 64-bit field 8 bytes little-endian (of its two's complement). Every input has
// its own encoding (remote's Check needs DecIn to give back the input EncIn encoded).
func Codec() remote.Codec {
	return remote.Codec{
		EncIn: func(in any) []byte {
			x := in.(In)
			b := make([]byte, 24)
			binary.LittleEndian.PutUint64(b[0:8], x.Op)
			binary.LittleEndian.PutUint64(b[8:16], uint64(x.A))
			binary.LittleEndian.PutUint64(b[16:24], uint64(x.B))
			return b
		},
		DecIn: func(b []byte) (any, bool) {
			if len(b) != 24 {
				return nil, false
			}
			return In{Op: binary.LittleEndian.Uint64(b[0:8]), A: int64(binary.LittleEndian.Uint64(b[8:16])),
				B: int64(binary.LittleEndian.Uint64(b[16:24]))}, true
		},
		EncOut: func(out any) []byte {
			o := out.(Out)
			b := make([]byte, 9)
			if o.Unknown {
				b[0] = 1
			}
			binary.LittleEndian.PutUint64(b[1:9], uint64(o.V))
			return b
		},
		DecOut: func(b []byte) (any, bool) {
			if len(b) != 9 || b[0] > 1 {
				return nil, false
			}
			return Out{Unknown: b[0] == 1, V: int64(binary.LittleEndian.Uint64(b[1:9]))}, true
		},
		IsRead:    func(in any) bool { return !isWrite(in.(In)) },
		Unknown:   func(in any) any { return Out{Unknown: true} },
		IsUnknown: func(out any) bool { return out.(Out).Unknown },
	}
}

// val is the value of client c's j-th operation, distinct for every (c, j) and never 0 (the
// register's initial value).
func val(c uint64, j uint64) int64 {
	return int64(100*(c+1) + j)
}

// Gen is client c's j-th input: a write of its own value, a read, a compare-and-swap that expects
// the client's own write, a read (and so on, every four operations). Clients 2p and 2p+1 start
// together: of their two concurrent writes, the later one's client swaps. Every value is distinct
// and non-zero.
func Gen(c uint64, j uint64) In {
	if j%4 == 0 {
		return In{Op: OpWrite, A: val(c, j), B: 0}
	}
	if j%4 == 2 {
		return In{Op: OpCAS, A: val(c, j-2), B: val(c, j)}
	}
	return In{Op: OpRead, A: 0, B: 0}
}

// gens numbers each client's inputs (remote's gen takes only the client).
type gens struct {
	mu *sync.Mutex
	n  []uint64
}

// next is client c's next input (Gen(c, j) for its j-th call). A c outside the clients (remote's
// gen contract allows any non-negative id) gets Gen(c, 0).
func (g *gens) next(c int) any {
	j := uint64(0)
	g.mu.Lock()
	if 0 <= c && c < len(g.n) {
		j = g.n[c]
		g.n[c] = j + 1
	}
	g.mu.Unlock()
	return Gen(uint64(c), j)
}

// attempt is CallMs as a duration.
func attempt() time.Duration {
	return time.Duration(CallMs) * time.Millisecond
}

// Orch is the orchestrator's program: it draws each client's number of operations, 1 to K, and
// panics unless porcupine accepts the history of the clients' operations.
func Orch() {
	g := &gens{mu: new(sync.Mutex), n: make([]uint64, NC)}
	gen := func(c int) any {
		return g.next(c)
	}
	remote.Check(Model(), ClientAddrs(), Codec(), gen, 1+rand.Intn(int(K)), attempt())
}

// client is client c's Gryff client: a connection to its replica, as Gryff's own client keeps one
// (clients.AbstractClient), opened at the client's first operation and after a failure, each time
// under a fresh Gryff client id (id), and the next request id (seq).
type client struct {
	conn net.Conn
	r    *bufio.Reader
	w    *bufio.Writer
	id   int32
	gen  uint64
	seq  int32
}

// Sys is client machine c's view of the deployment: the server machines' addresses, client c's
// Gryff client (used by its operations only, one at a time: remote.Serve serves one request at a
// time), and whether its first operation has waited for its start. mu guards the rest: remote's
// ServeClient takes the client's state only through a resource newClient can give any number of
// times (a lock), and serves one request at a time, so the lock is never contended.
type Sys struct {
	mu      *sync.Mutex
	c       uint64
	addrs   []string
	cl      *client
	started bool
	ops     uint64
}

// newSys is client c's side of the deployment at addrs (ServerAddrs, or kit_test.go's), with no
// connection yet.
func newSys(addrs []string, c uint64) *Sys {
	return &Sys{mu: new(sync.Mutex), c: c, addrs: addrs, cl: &client{}, started: false}
}

// noDep is the dependency of an operation of a non-sequential client (Gryff's emptyDep: key -1,
// no value), as Gryff's linearizable clients send.
func noDep() gryffproto.Dep {
	return gryffproto.Dep{Key: -1, Vt: gryffproto.ValTag{V: 0, T: gryffproto.Tag{Ts: 0, Cid: 0, Rmwc: 0}}}
}

// connect opens client c's connection to its replica, server 2 + c mod NReplicas, and sends its
// Gryff client id (4 bytes, little-endian, as Gryff's client's connectToReplica), a fresh one:
// c + NC * (the number of c's earlier connections).
func (sys *Sys) connect() bool {
	cl := sys.cl
	c := sys.c
	conn, err := net.DialTimeout("tcp", sys.addrs[1+c%NReplicas], time.Duration(DialMs)*time.Millisecond)
	if err != nil {
		return false
	}
	cl.id = int32(c + NC*cl.gen)
	cl.gen++
	cl.conn = conn
	cl.r = bufio.NewReader(conn)
	cl.w = bufio.NewWriter(conn)
	var b [4]byte
	binary.LittleEndian.PutUint32(b[:], uint32(cl.id))
	cl.w.Write(b[:])
	return true
}

// drop closes client c's connection; its next operation connects again, under a fresh id.
func (sys *Sys) drop() {
	cl := sys.cl
	cl.conn.Close()
	cl.conn = nil
}

// unknown is an operation's output when its outcome is unknown.
func unknown() any {
	return Out{Unknown: true}
}

// Op is client c's operation on the register (Gryff's key Key), as Gryff's client sends it to its
// replica in proxy mode (sendReadToNearest, sendWriteToNearest, sendRMWToNearest; the replica
// coordinates it): a Read, a Write or an RMW (a compare-and-swap) with a fresh request id, then
// the reply with that request id: a ReadReply's value, a WriteReply, an RMWReply. A reply with OK
// unset or an error is an unknown outcome: the connection is dropped (the client goes on under a
// fresh id). A reply to another request on the connection is skipped, as Gryff's client ignores a
// reply whose request it no longer waits for. Op waits for the reply without a deadline, as
// Gryff's client does: an operation never answered is the orchestrator's (its call gives up after
// CallMs: an unknown outcome; client machine c then serves no later request). (A read deadline
// would let a read time out in the middle of a reply and the next read go on: Gryff's Unmarshal
// ignores the errors of nested fields, and would decode bytes of the wrong field.) The first
// operation first waits for the client's start (Start).
func Op(s any, in any) any {
	sys := s.(*Sys)
	sys.mu.Lock()
	out := op(sys, in.(In))
	sys.mu.Unlock()
	return out
}

// op is Op under client c's lock. Client c answers at most K operations (the orchestrator's
// share of each client: remote.Check calls each client K times); any later one is unknown, so
// that no client sends Gryff more than K requests (the replicas' instance space is bounded by
// the requests of the run, decision D14 of the lab's proof).
func op(sys *Sys, x In) any {
	if sys.ops >= K {
		return unknown()
	}
	sys.ops++
	if !sys.started {
		sys.started = true
		time.Sleep(time.Duration(Start(sys.c)) * time.Millisecond)
	}
	cl := sys.cl
	if cl.conn == nil && !sys.connect() {
		return unknown()
	}
	cl.seq++
	req := cl.seq
	w := cl.w
	k := state.Key(Key)
	if x.Op == OpWrite {
		w.WriteByte(clientproto.Gryff_WRITE)
		m := &gryffproto.Write{RequestId: req, ClientId: cl.id, K: k, V: state.Value(x.A), D: noDep()}
		m.Marshal(w)
	} else if x.Op == OpCAS {
		w.WriteByte(clientproto.Gryff_RMW)
		m := &gryffproto.RMW{RequestId: req, ClientId: cl.id, K: k, D: noDep(),
			OldValue: state.Value(x.A), NewValue: state.Value(x.B)}
		m.Marshal(w)
	} else {
		w.WriteByte(clientproto.Gryff_READ)
		m := &gryffproto.Read{RequestId: req, ClientId: cl.id, K: k, D: noDep()}
		m.Marshal(w)
	}
	if err := w.Flush(); err != nil {
		sys.drop()
		return unknown()
	}
	for {
		code, err := cl.r.ReadByte()
		if err != nil {
			sys.drop()
			return unknown()
		}
		if code == clientproto.Gryff_READ_REPLY {
			rep := new(gryffproto.ReadReply)
			if err := rep.Unmarshal(cl.r); err != nil {
				sys.drop()
				return unknown()
			}
			if rep.RequestId == req && rep.ClientId == cl.id && !isWrite(x) {
				if rep.OK != 1 {
					sys.drop()
					return unknown()
				}
				return Out{V: int64(rep.V)}
			}
		} else if code == clientproto.Gryff_WRITE_REPLY {
			rep := new(gryffproto.WriteReply)
			if err := rep.Unmarshal(cl.r); err != nil {
				sys.drop()
				return unknown()
			}
			if rep.RequestId == req && rep.ClientId == cl.id && x.Op == OpWrite {
				if rep.OK != 1 {
					sys.drop()
					return unknown()
				}
				return Out{}
			}
		} else if code == clientproto.Gryff_RMW_REPLY {
			rep := new(gryffproto.RMWReply)
			if err := rep.Unmarshal(cl.r); err != nil {
				sys.drop()
				return unknown()
			}
			if rep.RequestId == req && x.Op == OpCAS {
				if rep.OK != 1 {
					sys.drop()
					return unknown()
				}
				return Out{}
			}
		} else {
			// not a reply Gryff sends a client of its proxy: the stream cannot be read on
			sys.drop()
			return unknown()
		}
	}
}

// Start is client c's delay before its first operation (Op): StartMs, for the replicas to register
// with the master and connect to each other (an operation before that is unknown), then a random
// 0 to (NC/2)*StaggerMs. Start matters only to tests (time is not modeled: the theorem allows any
// delay).
func Start(c uint64) uint64 {
	return StartMs + uint64(rand.Intn(int((NC/2)*StaggerMs)+1))
}

// Client is client machine c's program (c < NC): its Gryff client, served at its address in
// ClientAddrs. The client is made once, before serving (remote.ServeClient's newClient may be
// called any number of times as far as its contract says, and a second client c would reuse its
// Gryff client ids).
func Client(c uint64) {
	sys := newSys(ServerAddrs(), c)
	newClient := func(id int) any {
		return sys
	}
	remote.ServeClient(int(c), ClientAddrs()[c], newClient, Op, Codec(), attempt())
}

// Server is server machine id's program (1 <= id <= 1+NReplicas): id 1 is the master, ids 2.. the
// Gryff replicas. It never returns.
func Server(id uint64) {
	serve(id, ServerAddrs())
}

// serve is server id's program in the deployment at addrs (ServerAddrs, or kit_test.go's on
// loopback), listening on its address's port and, for a replica, its net/rpc server 1000 above.
// The master is master/main.go's (masterlib.NewMaster for NReplicas replicas, then Serve). A
// replica is server/main.go's Gryff replica (flag -t) as Gryff's experiments run it in proxy mode:
// it registers with the master (serverlib.RegisterWithMaster, which gives its replica id and the
// replicas' addresses), builds the replica (gryff.NewReplica: not thrifty, executing, replying
// after execution, no beacons, not durable, no statistics file, linearizable (not regular), proxy
// mode, conflicts possible, Gryff's message pattern (not epaxosMode), the EPaxos RMW handler,
// server/main.go's default timeouts, no broadcast optimization), registers it with net/rpc and
// serves net/rpc (serverlib.Serve); main.go's flags, profiling and signal handling are left out.
func serve(id uint64, addrs []string) {
	Register()
	hp := strings.Split(addrs[id-1], ":")
	port := atoi(hp[1])
	if id == 1 {
		m := masterlib.NewMaster(int(NReplicas), port)
		m.Serve()
		return
	}
	replicaId, nodeList := serverlib.RegisterWithMaster(hp[0], port, addrs[0])
	rep := gryff.NewReplica(replicaId, nodeList, false, true, true, false, false, "", false, true,
		false, false, gryff.EPAXOS, int(ShortcircuitMs), int(FastOverwriteMs), int(ForceWriteMs), false)
	if err := rpc.Register(rep); err != nil {
		return
	}
	serverlib.Serve(port + 1000)
}

// atoi is the decimal number s (its digits; anything else counts as 0).
func atoi(s string) int {
	n := 0
	for i := 0; i < len(s); i++ {
		d := int(s[i]) - int('0')
		if d >= 0 && d <= 9 {
			n = n*10 + d
		}
	}
	return n
}
