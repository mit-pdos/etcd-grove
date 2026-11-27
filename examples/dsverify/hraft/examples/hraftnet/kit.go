// Package hraftnet is the hraft kit (notes/dsv-hraft.md), an instance of examples/lib/remote:
// hashicorp/raft's servers over net/rpc (the transport of package rpctransport), each with a
// one-register state machine and an API service, five clients each on a machine of its own, and
// an orchestrator that changes the cluster's membership and checks the clients' history with
// porcupine. 1+NC+NS machines, each a command of cmd/:
//
//   - the orchestrator (Orch): picks the first configuration's size n0 (3 or 5 voters) at random
//     and sends it to the servers (configure); starts the admin goroutine, which forever asks a
//     random server (or the leader a random server names) for a random membership change of a
//     random server (AddVoter, AddNonvoter, DemoteVoter, RemoveServer), a leadership transfer or a
//     snapshot; then remote.Check of NC
//     clients' operations against the register with pending writes (Model);
//   - client machine c (Client): remote.ServeClient whose operation is a write through the log
//     (Apply), or a read in one of three ways: through the log, after a Barrier, or with
//     VerifyLeader after a barrier of the server's term (op), each tried at the servers in turn
//     until one takes it;
//   - server machine id, 1 <= id <= NS (Server, server.go): raft over this kit's net/rpc
//     transport (package rpctransport), bootstrapped with servers 1..n0 as voters if id <= n0 (the
//     others start empty, non-members until a leader adds them), with the register as its state
//     machine and its API (package service).
//
// A write whose outcome is unknown (appended but its future failed, or no answer) is answered
// Out{Unknown: true}: it may have taken effect, may take effect later, or never. A read that no
// server answers is unknown too, and constrains nothing. Faults (lost, late, cut connections)
// come from the network; nothing here makes any.
package hraftnet

import (
	"io"
	"net"
	"strconv"
	"time"

	"github.com/anishathalye/porcupine"
	"github.com/goose-lang/primitive"
	"github.com/hashicorp/raft/examples/hraftnet/rpctransport"
	"github.com/hashicorp/raft/examples/hraftnet/service"
	"github.com/mit-pdos/etcd-grove/examples/lib/remote"
)

// rnd is a number below n, at random (in the theorem, any).
func rnd(n uint64) uint64 {
	return primitive.RandomUint64() % n
}

// --- the configuration: the first configuration's size n0

// confAck is a server's answer to a configuration it accepted.
const confAck = 0x6b

// chooseN0 is the first configuration's number of voters: 3 or 5, at random.
func chooseN0() uint64 {
	return 3 + 2*rnd(2)
}

// configure sends n0 to every server machine, each until it acknowledges it.
func configure(n0 uint64) {
	cfgs := ConfAddrs()
	for i := uint64(1); i <= NS; i++ {
		for !sendConf(cfgs[i-1], n0) {
			time.Sleep(time.Duration(RetryMs) * time.Millisecond)
		}
	}
}

// sendConf sends n0 (one byte) to the machine at addr and waits for its acknowledgment; true if
// acknowledged.
func sendConf(addr string, n0 uint64) bool {
	c, err := net.Dial("tcp", addr)
	if err != nil {
		return false
	}
	ok := false
	if _, err := c.Write([]byte{byte(n0)}); err == nil {
		var a [1]byte
		if _, err := io.ReadFull(c, a[:]); err == nil && a[0] == confAck {
			ok = true
		}
	}
	c.Close()
	return ok
}

// awaitConf listens on addr (retrying a failed Listen) and answers every configuration it reads
// (a size from 1 to NS) with an acknowledgment (the orchestrator sends again until it has one);
// the first is sent on ch. A connection that fails, or whose byte is not a size, is closed
// without an answer.
func awaitConf(addr string, ch chan uint64) {
	l := listen(addr)
	first := true
	for {
		c, err := l.Accept()
		if err != nil {
			continue
		}
		var b [1]byte
		if _, err := io.ReadFull(c, b[:]); err == nil {
			n0 := uint64(b[0])
			if 1 <= n0 && n0 <= NS {
				if first {
					ch <- n0
					first = false
				}
				c.Write([]byte{confAck})
			}
		}
		c.Close()
	}
}

// --- the model: one register with pending writes

// In is an operation's input: a write of V (Put), or a read in one of the ways (Way: WayLog,
// WayBarrier, WayVerify).
type In struct {
	Put bool
	Way uint64
	V   string
}

// WayLog is a read through the log (a get command).
const WayLog uint64 = 0

// Out is an operation's output: unknown, or a write's success, or a read's answer (Found, and
// the value V if found).
type Out struct {
	Unknown bool
	Found   bool
	V       string
}

// State is the model's state: the register (Present, V) and the writes pending.
type State struct {
	Present bool
	V       string
	Pend    []string
}

// pushPend is p with v appended (a fresh slice).
func pushPend(p []string, v string) []string {
	q := make([]string, len(p)+1)
	copy(q, p)
	q[len(p)] = v
	return q
}

// findPend is the index of a write of v pending in p, and whether there is one.
func findPend(p []string, v string) (int, bool) {
	for i := 0; i < len(p); i++ {
		if p[i] == v {
			return i, true
		}
	}
	return 0, false
}

// erasePend is p without its element i (a fresh slice).
func erasePend(p []string, i int) []string {
	q := make([]string, 0, len(p))
	for j := 0; j < len(p); j++ {
		if j != i {
			q = append(q, p[j])
		}
	}
	return q
}

// step is the model's step from s on input in with output o: an unknown write becomes pending,
// an unknown read changes nothing; a write sets the register; a read answers the register's
// value, or the value of a pending write, which takes effect then.
func step(s State, in In, o Out) (bool, State) {
	if o.Unknown {
		if in.Put {
			return true, State{Present: s.Present, V: s.V, Pend: pushPend(s.Pend, in.V)}
		}
		return true, s
	}
	if in.Put {
		if o.Found || o.V != "" {
			return false, s
		}
		return true, State{Present: true, V: in.V, Pend: s.Pend}
	}
	if !o.Found {
		if o.V != "" {
			return false, s
		}
		return !s.Present, s
	}
	if s.Present && s.V == o.V {
		return true, s
	}
	if i, ok := findPend(s.Pend, o.V); ok {
		return true, State{Present: true, V: o.V, Pend: erasePend(s.Pend, i)}
	}
	return false, s
}

// Model is the register with pending writes, as a porcupine model. Its Equal is always false
// (porcupine then never merges two states it reached; only slower): a state does not determine the
// executions it stands for (a pending write may have taken effect before a later write overwrote
// it, or not), so equal states need not be the same model state.
func Model() porcupine.Model {
	return porcupine.Model{
		Init: func() any { return State{} },
		Step: func(state, input, output any) (bool, any) {
			ok, s := step(state.(State), input.(In), output.(Out))
			return ok, s
		},
		Equal: func(a, b any) bool { return false },
	}
}

// encStr appends s to b, its length (one byte) first; s is shorter than 256 bytes.
func encStr(b []byte, s string) []byte {
	b = append(b, byte(len(s)))
	return append(b, []byte(s)...)
}

// decStr is the string encStr put at b's start and the rest of b, if b starts with one.
func decStr(b []byte) (string, []byte, bool) {
	if len(b) < 1 || uint64(len(b)) < 1+uint64(b[0]) {
		return "", nil, false
	}
	n := uint64(b[0])
	return string(b[1 : 1+n]), b[1+n:], true
}

// flag is 1 for true, 0 for false.
func flag(x bool) byte {
	if x {
		return 1
	}
	return 0
}

// Codec is the model's inputs and outputs on the wire between the orchestrator and the client
// machines: an input is the put flag, the way, then V; an output the unknown and found flags,
// then V.
func Codec() remote.Codec {
	return remote.Codec{
		EncIn: func(in any) []byte {
			x := in.(In)
			return encStr([]byte{flag(x.Put), byte(x.Way)}, x.V)
		},
		DecIn: func(b []byte) (any, bool) {
			if len(b) < 2 || b[0] > 1 || b[1] > 2 {
				return nil, false
			}
			v, r, ok := decStr(b[2:])
			if !ok || len(r) != 0 {
				return nil, false
			}
			return In{Put: b[0] == 1, Way: uint64(b[1]), V: v}, true
		},
		EncOut: func(out any) []byte {
			o := out.(Out)
			return encStr([]byte{flag(o.Unknown), flag(o.Found)}, o.V)
		},
		DecOut: func(b []byte) (any, bool) {
			if len(b) < 2 || b[0] > 1 || b[1] > 1 {
				return nil, false
			}
			v, r, ok := decStr(b[2:])
			if !ok || len(r) != 0 {
				return nil, false
			}
			return Out{Unknown: b[0] == 1, Found: b[1] == 1, V: v}, true
		},
		IsRead:    func(in any) bool { return !in.(In).Put },
		Unknown:   func(in any) any { return Out{Unknown: true} },
		IsUnknown: func(out any) bool { return out.(Out).Unknown },
	}
}

// Gen is a client's next input, at random: a write (one in two) of a value "v<c>.<n>" (n random),
// or a read in a random way.
func Gen(c int) any {
	n := primitive.RandomUint64()
	if n%2 == 0 {
		return In{Put: true, Way: 0, V: "v" + strconv.Itoa(c) + "." + strconv.Itoa(int((n/2)%1000000))}
	}
	return In{Put: false, Way: (n / 2) % 3, V: ""}
}

// attempt is AttemptMs as a duration.
func attempt() time.Duration {
	return time.Duration(AttemptMs) * time.Millisecond
}

// --- the orchestrator

// Orch is the orchestrator machine's program: it picks n0 and sends it, starts the admin, then
// checks NC clients' operations, a random 1 to MaxOps each (remote.Check panics if porcupine
// rejects the history).
func Orch() {
	configure(chooseN0())
	Register()
	go admin()
	remoteCheck(chooseOps())
}

// chooseOps is the number of operations each client makes: 1 to MaxOps, at random (as n0 and
// raft's options are: the theorem covers every number drawn).
func chooseOps() uint64 {
	return 1 + rnd(MaxOps)
}

// remoteCheck checks NC clients' operations, ops each: remote.Check panics if porcupine rejects
// the history (it runs to completion, with no timeout).
func remoteCheck(ops uint64) {
	remote.Check(Model(), ClientAddrs(), Codec(), Gen, int(ops), attempt())
}

// The admin's requests (API methods), by kind.
func adminMethods() []string {
	return []string{"API.AddVoter", "API.AddNonvoter", "API.DemoteVoter", "API.RemoveServer",
		"API.LeadershipTransfer", "API.Snapshot"}
}

// admin forever asks a server, AdminMs apart at most, for one of: AddVoter, AddNonvoter,
// DemoteVoter or RemoveServer of a random server s (any of them: a non-member, a non-voter, a
// voter, the server asked itself; raft makes one change at a time, and a server that does not lead
// refuses); a leadership transfer (to the server raft picks, or to s); a snapshot. The server
// asked is a random one, or (one time in two) the leader a random one names (adminTarget). A
// removed server keeps running and may be added again. Every request waits for its answer
// (APITimeoutMs at most); its outcome does not matter.
func admin() {
	conns := serverConns()
	ms := adminMethods()
	for {
		time.Sleep(time.Duration(rnd(AdminMs)) * time.Millisecond)
		j := adminTarget(conns)
		k := rnd(uint64(len(ms)))
		s := 1 + rnd(NS)
		args := &service.AdminArgs{ID: string(serverID(s)), Addr: string(serverAddr(s))}
		if k == 4 && rnd(2) == 0 {
			args = &service.AdminArgs{ID: "", Addr: ""}
		}
		conns[j-1].Call(ms[k], args, new(service.AdminReply), apiTimeout())
	}
}

// adminTarget is the server the admin asks: a random server j, or, one time in two, the leader j
// names (its Status), if it names one of the servers.
func adminTarget(conns []*rpctransport.Conn) uint64 {
	j := 1 + rnd(NS)
	if rnd(2) == 0 {
		return j
	}
	st := new(service.StatusReply)
	if conns[j-1].Call("API.Status", &service.AdminArgs{ID: "", Addr: ""}, st, apiTimeout()) != rpctransport.CallOK {
		return j
	}
	if st.Leader {
		return j
	}
	for i := uint64(1); i <= NS; i++ {
		if string(serverID(i)) == st.LeaderID {
			return i
		}
	}
	return j
}

// --- the clients

// serverConns is a connection to every server's API (index id-1).
func serverConns() []*rpctransport.Conn {
	var cs []*rpctransport.Conn
	for _, a := range ServerAddrs() {
		cs = append(cs, rpctransport.NewConn(a))
	}
	return cs
}

// apiTimeout is how long a call to a server's API waits for its answer.
func apiTimeout() time.Duration {
	return time.Duration(APITimeoutMs) * time.Millisecond
}

// Sys is a client machine's view of the deployment: its connections to the servers, the server
// it tries first, and its operations' count (an operation's id is the client's and the count's).
type Sys struct {
	c     uint64
	conns []*rpctransport.Conn
	j     uint64
	seq   uint64
}

// opID is the 8-byte id of client c's operation seq: c in the top byte, seq below.
func opID(c uint64, seq uint64) []byte {
	x := c<<56 | seq%(1<<56)
	b := make([]byte, 8)
	for i := uint64(0); i < 8; i++ {
		b[i] = byte(x >> (56 - 8*i))
	}
	return b
}

// command is the log command of client c's operation seq on input x (package service's format):
// a put with its value, or a get.
func command(c uint64, seq uint64, x In) []byte {
	if x.Put {
		return append(append([]byte{service.CmdPut}, opID(c, seq)...), []byte(x.V)...)
	}
	return append([]byte{service.CmdGet}, opID(c, seq)...)
}

// try is one attempt of operation x at server j: its output, and whether it is final (else the
// attempt had no effect, and the operation is tried at the next server). A write or a log read
// is an Apply: final when done (the FSM's answer) or unknown; a read outside the log is final
// when answered; a call that was sent but got no answer is final and unknown.
func (s *Sys) try(j uint64, cmd []byte, x In) (Out, bool) {
	if x.Put || x.Way == WayLog {
		reply := new(service.ApplyReply)
		res := s.conns[j-1].Call("API.Apply", &service.ApplyArgs{Data: cmd}, reply, apiTimeout())
		if res == rpctransport.CallNotSent {
			return Out{}, false
		}
		if res == rpctransport.CallFailed {
			return Out{Unknown: true}, true
		}
		if reply.Status == service.StatusNoEffect {
			return Out{}, false
		}
		if reply.Status != service.StatusDone {
			return Out{Unknown: true}, true
		}
		if x.Put {
			return Out{}, true
		}
		return Out{Found: reply.Found, V: reply.V}, true
	}
	reply := new(service.ReadReply)
	res := s.conns[j-1].Call("API.Read", &service.ReadArgs{Way: x.Way}, reply, apiTimeout())
	if res == rpctransport.CallNotSent {
		return Out{}, false
	}
	if res == rpctransport.CallFailed {
		return Out{Unknown: true}, true
	}
	if !reply.Ok {
		return Out{}, false
	}
	return Out{Found: reply.Found, V: reply.V}, true
}

// op is the client's operation x: tried at the servers in turn, starting at the one that took the
// last operation, at most Tries times, RetryMs apart; unknown if no server took it.
func (s *Sys) op(x In) Out {
	s.seq++
	cmd := command(s.c, s.seq, x)
	for t := uint64(0); t < Tries; t++ {
		o, final := s.try(s.j, cmd, x)
		if final {
			return o
		}
		s.j = 1 + s.j%NS
		time.Sleep(time.Duration(RetryMs) * time.Millisecond)
	}
	return Out{Unknown: true}
}

// Client is client machine c's program: remote.ServeClient whose client is a fresh Sys (its first
// server at random) and whose operation is op. It never returns.
func Client(c uint64) {
	Register()
	newClient := func(id int) any {
		return &Sys{c: c, conns: serverConns(), j: 1 + rnd(NS)}
	}
	opc := func(sys any, in any) any {
		return sys.(*Sys).op(in.(In))
	}
	remote.ServeClient(int(c), ClientAddrs()[c], newClient, opc, Codec(), attempt())
}
