// Package craqnet is the craq kit (dsverify-lab's craq-bump-1, notes/dsv-craq.md) as an instance
// of examples/lib/remote: despreston/go-craq's chain replication over net/rpc (over HTTP's
// CONNECT, as go-craq's cmd/node and cmd/coordinator serve it), a key-value map whose clients each
// run on a machine of their own, checked by porcupine on an orchestrator machine. 1+NC+1+MaxChain
// machines, each a command of cmd/:
//
//   - the orchestrator (Orch): chooses the configuration and the removals at random and sends them
//     to the machines that need them (configure), then remote.Check of NC clients' K operations
//     each, made at the clients' own machines, against the key-value map with pending puts (Model);
//   - client machine c (Client): remote.ServeClient whose operation is a put through the
//     coordinator's Write or a get at a chain node's Read, each on a connection of its own (op);
//     the machine also asks the coordinator for the removals the orchestrator planned for it;
//   - server machine 1 (Server(1)): the coordinator (cmd/coordinator's main without flags);
//   - server machine id, 2 <= id <= MaxChain+1 (Server(id)): a chain node over the in-memory store
//     (cmd/node's main without flags), once the configuration has arrived, if the chain has it.
//
// The configuration (the lab's): a chain of 3, 4 or 5 nodes (on server machines 2..N+1; with fewer
// than MaxChain, the other chain machines only wait), how many of them join only after the clients
// have started (0, 1 or 2), and where the clients read (each at a chain node of its own, CRAQ's
// apportioned reads, or all at the chain's tail when the clients start, chain replication's
// reads). One or two removals, each asked for by a client machine once a random number of its
// client's operations have ended: the coordinator's RemoveNode of a random chain node, over net/rpc,
// as its ping loop calls it when a ping fails.
//
// A put whose call fails has an unknown outcome (Out{Unknown: true}): it may have taken effect,
// may take effect later, or never. A get that fails is retried by remote (a read); if no attempt
// answers, its outcome is unknown too, and constrains nothing.
//
// (dsverify-lab's kit ran its own remote driver, recorder and key-value checker, with Gen's
// inputs a function of the client and the round; here they are remote's, lintest's and
// porcupine's, and remote's generator sees the client only, so Gen picks at random.)
package craqnet

import (
	"io"
	"log"
	"net"
	"net/http"
	"net/rpc"
	"sync"
	"time"

	"github.com/anishathalye/porcupine"
	"github.com/despreston/go-craq/coordinator"
	"github.com/despreston/go-craq/node"
	"github.com/despreston/go-craq/store/kv"
	"github.com/despreston/go-craq/transport/netrpc"
	"github.com/goose-lang/primitive"
	"github.com/mit-pdos/etcd-grove/examples/lib/remote"
)

// The configuration: NC clients, K operations each, the most chain nodes MaxChain, the chain
// machines' join delays (JoinMs apart, the late ones LateMs apart after StartMs), the keys
// NKeys, the wait before a retry RetryMs, an idle machine's sleep IdleMs.
const (
	NC       uint64 = 5
	K        uint64 = 6
	MaxChain uint64 = 5
	JoinMs   uint64 = 300
	LateMs   uint64 = 300
	StartMs  uint64 = 2000
	NKeys    uint64 = 2
	RetryMs  uint64 = 100
	IdleMs   uint64 = 10000
)

// AttemptMs bounds one call between the orchestrator and a client machine.
const AttemptMs uint64 = 5000

// ServerAddrs is the server machines' net/rpc addresses: index 0 the coordinator (server
// machine 1), index k-1 chain machine k (2 <= k <= MaxChain+1).
func ServerAddrs() []string {
	return []string{
		"127.0.0.1:7501",
		"127.0.0.1:7502",
		"127.0.0.1:7503",
		"127.0.0.1:7504",
		"127.0.0.1:7505",
		"127.0.0.1:7506",
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
	}
}

// ConfAddrs is the configuration addresses: index c client machine c's (c < NC), index NC+k-1
// chain machine k's (2 <= k <= MaxChain+1; index NC, the coordinator's, is not used).
func ConfAddrs() []string {
	return []string{
		"127.0.0.1:7521",
		"127.0.0.1:7522",
		"127.0.0.1:7523",
		"127.0.0.1:7524",
		"127.0.0.1:7525",
		"127.0.0.1:7530",
		"127.0.0.1:7531",
		"127.0.0.1:7532",
		"127.0.0.1:7533",
		"127.0.0.1:7534",
		"127.0.0.1:7535",
	}
}

// confAck is a machine's answer to a configuration it accepted.
const confAck = 0x6b

// ConfLen is a configuration message's length in bytes (Conf.encode).
const ConfLen = 8

// MaxRemovals is the most removals plan picks, and the most a message carries.
const MaxRemovals = 2

// Conf is a configuration of the deployment.
type Conf struct {
	N        uint64 // chain nodes: 3, 4 or 5 (server machines 2..N+1)
	Late     uint64 // of them, the last Late (0, 1 or 2) join after the clients have started
	ReadTail uint64 // 1: every get reads at machine N+1-Late (the tail when the clients start); 0: client c's at machine 2 + c mod N
}

// removal is a planned removal: once After of client Client's operations have ended, client
// machine Client asks the coordinator to remove chain machine Node.
type removal struct {
	Client uint64
	Node   uint64
	After  uint64
}

// rnd is a number below n, at random (in the theorem, any).
func rnd(n uint64) uint64 {
	return primitive.RandomUint64() % n
}

// choose picks a configuration at random.
func choose() Conf {
	return Conf{N: 3 + rnd(3), Late: rnd(3), ReadTail: rnd(2)}
}

// plan picks one or two removals at random: each asked for by a random client machine, of a
// random chain node of conf (one that has not joined yet, or was removed already, is unknown to
// the coordinator, which refuses it), once 1 to K-1 of that client's operations have ended.
func plan(conf Conf) []removal {
	var rs []removal
	n := 1 + rnd(MaxRemovals)
	for i := uint64(0); i < n; i++ {
		rs = append(rs, removal{Client: rnd(NC), Node: 2 + rnd(conf.N), After: 1 + rnd(K-1)})
	}
	return rs
}

// mine is the removals of rs that client c asks for, in rs's order.
func mine(rs []removal, c uint64) []removal {
	var m []removal
	for _, r := range rs {
		if r.Client == c {
			m = append(m, r)
		}
	}
	return m
}

// encode is c with the removals rs (at most MaxRemovals, all of one client) on the wire: ConfLen
// bytes, N, Late, ReadTail, the number of removals, then each removal's Node and After (zero
// bytes for the ones missing).
func (c Conf) encode(rs []removal) []byte {
	b := make([]byte, ConfLen)
	b[0] = byte(c.N)
	b[1] = byte(c.Late)
	b[2] = byte(c.ReadTail)
	b[3] = byte(len(rs))
	for i, r := range rs {
		b[4+2*i] = byte(r.Node)
		b[5+2*i] = byte(r.After)
	}
	return b
}

// decode is the configuration and the removals b encodes, if b is a message configure can send
// (the removals' Client, which is not on the wire, is 0: a client machine's are its own).
func decode(b []byte) (Conf, []removal, bool) {
	conf := Conf{N: uint64(b[0]), Late: uint64(b[1]), ReadTail: uint64(b[2])}
	if conf.N < 3 || conf.N > MaxChain || conf.Late > 2 || conf.ReadTail > 1 || uint64(b[3]) > MaxRemovals {
		return conf, nil, false
	}
	var rs []removal
	for i := uint64(0); i < uint64(b[3]); i++ {
		r := removal{Client: 0, Node: uint64(b[4+2*i]), After: uint64(b[5+2*i])}
		if r.Node < 2 || r.Node > conf.N+1 || r.After < 1 || r.After >= K {
			return conf, nil, false
		}
		rs = append(rs, r)
	}
	return conf, rs, true
}

// String is c for the log.
func (c Conf) String() string {
	reads := "apportioned reads"
	if c.ReadTail == 1 {
		reads = "reads at node " + digit(c.N+1-c.Late)
	}
	return "chain of " + digit(c.N) + ", " + digit(c.Late) + " joining late, " + reads
}

// configure sends the configuration conf to every client machine, each with the removals of rs it
// asks for, and to chain machines 2..conf.N+1, each until it acknowledges it.
func configure(conf Conf, rs []removal) {
	log.Println("craqnet: configuration: " + conf.String() + ", " + digit(uint64(len(rs))) + " removals")
	cfgs := ConfAddrs()
	for c := uint64(0); c < NC; c++ {
		for !sendConf(cfgs[c], conf.encode(mine(rs, c))) {
			time.Sleep(time.Duration(RetryMs) * time.Millisecond)
		}
	}
	for k := uint64(2); k <= conf.N+1; k++ {
		for !sendConf(cfgs[NC+k-1], conf.encode(nil)) {
			time.Sleep(time.Duration(RetryMs) * time.Millisecond)
		}
	}
}

// sendConf sends the configuration message b to the machine at addr and waits for its
// acknowledgment; true if acknowledged.
func sendConf(addr string, b []byte) bool {
	c, err := net.Dial("tcp", addr)
	if err != nil {
		return false
	}
	ok := false
	if _, err := c.Write(b); err == nil {
		var a [1]byte
		if _, err := io.ReadFull(c, a[:]); err == nil && a[0] == confAck {
			ok = true
		}
	}
	c.Close()
	return ok
}

// msg is a configuration message as a machine decoded it.
type msg struct {
	conf Conf
	rs   []removal
}

// awaitConf listens on addr (retrying a failed Listen) and answers every configuration message it
// reads with an acknowledgment (the orchestrator sends again until it has one); the first is sent
// on ch. A connection that fails, or whose bytes are not a configuration message, is closed
// without an answer.
func awaitConf(addr string, ch chan msg) {
	l, err := net.Listen("tcp", addr)
	for err != nil {
		time.Sleep(time.Duration(RetryMs) * time.Millisecond)
		l, err = net.Listen("tcp", addr)
	}
	first := true
	for {
		c, err := l.Accept()
		if err != nil {
			continue
		}
		var b [ConfLen]byte
		if _, err := io.ReadFull(c, b[:]); err == nil {
			if conf, rs, ok := decode(b[:]); ok {
				if first {
					ch <- msg{conf: conf, rs: rs}
					first = false
				}
				c.Write([]byte{confAck})
			}
		}
		c.Close()
	}
}

// In is an operation's input: a put of V at K, or a get of K.
type In struct {
	Put bool
	K   string
	V   string
}

// Out is an operation's output: unknown (a put or get whose outcome is unknown), or a put's
// success, or a get's answer (Found, and the value V if found).
type Out struct {
	Unknown bool
	Found   bool
	V       string
}

// pend is a put whose outcome is unknown: it may take effect at any later point, or never.
type pend struct {
	K string
	V string
}

// State is the model's state: the map (a key it lacks is not found) and the puts pending.
type State struct {
	M    map[string]string
	Pend []pend
}

// copyMap is a fresh map with m's contents.
func copyMap(m map[string]string) map[string]string {
	c := make(map[string]string)
	for k, v := range m {
		c[k] = v
	}
	return c
}

// set is s with k mapped to v (a fresh map).
func set(m map[string]string, k string, v string) map[string]string {
	c := copyMap(m)
	c[k] = v
	return c
}

// pushPend is p with (k, v) appended (a fresh slice).
func pushPend(p []pend, k string, v string) []pend {
	q := make([]pend, len(p)+1)
	copy(q, p)
	q[len(p)] = pend{K: k, V: v}
	return q
}

// findPend is the index of a put of v at k pending in p, and whether there is one.
func findPend(p []pend, k string, v string) (int, bool) {
	for i := 0; i < len(p); i++ {
		if p[i].K == k && p[i].V == v {
			return i, true
		}
	}
	return 0, false
}

// erasePend is p without its element i (a fresh slice).
func erasePend(p []pend, i int) []pend {
	q := make([]pend, 0, len(p))
	for j := 0; j < len(p); j++ {
		if j != i {
			q = append(q, p[j])
		}
	}
	return q
}

// step is the model's step from s on input in with output o: an unknown put becomes pending, an
// unknown get changes nothing; a put sets its key; a get answers its key's value, or the value of
// a put pending at its key, which takes effect then.
func step(s State, in In, o Out) (bool, State) {
	if o.Unknown {
		if in.Put {
			return true, State{M: s.M, Pend: pushPend(s.Pend, in.K, in.V)}
		}
		return true, s
	}
	if in.Put {
		if o.Found || o.V != "" {
			return false, s
		}
		return true, State{M: set(s.M, in.K, in.V), Pend: s.Pend}
	}
	v, found := s.M[in.K]
	if !o.Found {
		if o.V != "" {
			return false, s
		}
		return !found, s
	}
	if found && v == o.V {
		return true, s
	}
	if i, ok := findPend(s.Pend, in.K, o.V); ok {
		return true, State{M: set(s.M, in.K, o.V), Pend: erasePend(s.Pend, i)}
	}
	return false, s
}

// within says whether every key of a has the same value in b.
func within(a, b map[string]string) bool {
	ok := true
	for k, v := range a {
		w, found := b[k]
		if !found || w != v {
			ok = false
		}
	}
	return ok
}

// equal says whether a and b are the same state (the pending puts in the same order).
func equal(a State, b State) bool {
	if !within(a.M, b.M) || !within(b.M, a.M) || len(a.Pend) != len(b.Pend) {
		return false
	}
	for i := 0; i < len(a.Pend); i++ {
		if a.Pend[i] != b.Pend[i] {
			return false
		}
	}
	return true
}

// Model is the key-value map with pending puts, as a porcupine model.
func Model() porcupine.Model {
	return porcupine.Model{
		Init: func() any { return State{M: make(map[string]string)} },
		Step: func(state, input, output any) (bool, any) {
			ok, s := step(state.(State), input.(In), output.(Out))
			return ok, s
		},
		Equal: func(a, b any) bool { return equal(a.(State), b.(State)) },
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
// machines: an input is the put flag, then K and V; an output the unknown and found flags, then V.
func Codec() remote.Codec {
	return remote.Codec{
		EncIn: func(in any) []byte {
			x := in.(In)
			return encStr(encStr([]byte{flag(x.Put)}, x.K), x.V)
		},
		DecIn: func(b []byte) (any, bool) {
			if len(b) < 1 || b[0] > 1 {
				return nil, false
			}
			k, r, ok := decStr(b[1:])
			if !ok {
				return nil, false
			}
			v, r2, ok2 := decStr(r)
			if !ok2 || len(r2) != 0 {
				return nil, false
			}
			return In{Put: b[0] == 1, K: k, V: v}, true
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

// digit is n's last decimal digit.
func digit(n uint64) string {
	return string([]byte{byte('0' + n%10)})
}

// Gen is a client's next input, at random: a put (one in two) of a value "v<c><d>" or a get, of
// one of the keys "k0".."k<NKeys-1>".
func Gen(c int) any {
	n := primitive.RandomUint64()
	k := "k" + digit((n/2)%NKeys)
	if n%2 == 0 {
		return In{Put: true, K: k, V: "v" + digit(uint64(c)) + digit(n/(2*NKeys))}
	}
	return In{Put: false, K: k, V: ""}
}

// attempt is AttemptMs as a duration.
func attempt() time.Duration {
	return time.Duration(AttemptMs) * time.Millisecond
}

// Orch is the orchestrator machine's program: it chooses the configuration and the removals,
// sends them, waits StartMs for the chain to form, then checks NC clients' K operations each
// (remote.Check panics if porcupine rejects the history). The wait matters only to tests (time is
// not modeled: the theorem allows any delay).
func Orch() {
	conf := choose()
	configure(conf, plan(conf))
	time.Sleep(time.Duration(StartMs) * time.Millisecond)
	remote.Check(Model(), ClientAddrs(), Codec(), Gen, int(K), attempt())
}

// Sys is a client machine's view of the deployment: the configuration, and the number of its
// client's operations that have ended.
type Sys struct {
	conf  Conf
	mu    sync.Mutex
	ended uint64
}

// newSys is client machine c's side of the deployment: it waits for the configuration, registers
// the net/rpc codec (the model's; nothing in the real build) and starts the removals this machine
// asks for.
func newSys(c uint64) *Sys {
	ch := make(chan msg, 1)
	go awaitConf(ConfAddrs()[c], ch)
	m := <-ch
	Register()
	s := &Sys{conf: m.conf}
	go s.remove(m.rs)
	return s
}

// end counts an operation that ended (returned or not).
func (s *Sys) end() {
	s.mu.Lock()
	s.ended++
	s.mu.Unlock()
}

// remove makes the removals rs: once each one's number of this client's operations have ended,
// it asks the coordinator to remove the chain node, as the coordinator's ping loop does when a
// ping fails (CoordinatorClient.RemoveNode over net/rpc, on a connection of its own); a failed
// call is not retried.
func (s *Sys) remove(rs []removal) {
	for _, r := range rs {
		for {
			s.mu.Lock()
			e := s.ended
			s.mu.Unlock()
			if e >= r.After {
				break
			}
			time.Sleep(time.Duration(RetryMs) * time.Millisecond)
		}
		log.Println("craqnet: removing node " + digit(r.Node))
		cc := netrpc.NewCoordinatorClient()
		if err := cc.Connect(ServerAddrs()[0]); err == nil {
			cc.RemoveNode(ServerAddrs()[r.Node-1])
			cc.Close()
		}
	}
}

// errNotFound is go-craq's Node.Read error for a key its store does not have.
const errNotFound = "key doesn't exist"

// readAt is the chain machine client c's gets read at.
func (s *Sys) readAt(c uint64) uint64 {
	if s.conf.ReadTail == 1 {
		return s.conf.N + 1 - s.conf.Late
	}
	return 2 + c%s.conf.N
}

// op is client c's operation, on a connection of its own: a put is the coordinator's Write, a
// get is a chain node's Read (readAt). Out{Unknown: true} on any error but a get's errNotFound.
func op(s *Sys, c uint64, x In) Out {
	if x.Put {
		cc := netrpc.NewCoordinatorClient()
		if err := cc.Connect(ServerAddrs()[0]); err != nil {
			return Out{Unknown: true}
		}
		err := cc.Write(x.K, []byte(x.V))
		cc.Close()
		if err != nil {
			return Out{Unknown: true}
		}
		return Out{}
	}
	nc := netrpc.NewNodeClient()
	if err := nc.Connect(ServerAddrs()[s.readAt(c)-1]); err != nil {
		return Out{Unknown: true}
	}
	_, v, err := nc.Read(x.K)
	nc.Close()
	if err != nil {
		if se, ok := err.(rpc.ServerError); ok && string(se) == errNotFound {
			return Out{}
		}
		return Out{Unknown: true}
	}
	return Out{Found: true, V: string(v)}
}

// Client is client machine c's program: remote.ServeClient with its view of the deployment
// (newSys) and op. It never returns.
func Client(c uint64) {
	newClient := func(id int) any {
		return newSys(c)
	}
	opc := func(sys any, in any) any {
		s := sys.(*Sys)
		o := op(s, c, in.(In))
		s.end()
		return o
	}
	remote.ServeClient(int(c), ClientAddrs()[c], newClient, opc, Codec(), attempt())
}

// joinMs is chain machine id's delay, after the configuration arrived, before it announces itself
// to the coordinator (Node.Start's AddNode): JoinMs apart in id order, and the last conf.Late
// nodes only after the clients have started (StartMs, then LateMs apart).
func joinMs(id uint64, conf Conf) uint64 {
	i := id - 2
	early := conf.N - conf.Late
	if i < early {
		return (i + 1) * JoinMs
	}
	return StartMs + (i-early+1)*LateMs
}

// Server is server machine id's program (1 <= id <= MaxChain+1): id 1 is cmd/coordinator's main;
// a chain machine waits for the configuration, then runs cmd/node's main over the in-memory store
// if id <= N+1, else only waits.
func Server(id uint64) {
	Register()
	addr := ServerAddrs()[id-1]
	if id == 1 {
		c := coordinator.New(netrpc.NewNodeClient)
		cb := netrpc.CoordinatorBinding{Svc: c}
		if err := rpc.RegisterName("RPC", &cb); err != nil {
			return
		}
		rpc.HandleHTTP()
		go c.Start()
		http.ListenAndServe(addr, nil)
		return
	}
	ch := make(chan msg, 1)
	go awaitConf(ConfAddrs()[NC+id-1], ch)
	m := <-ch
	if id <= m.conf.N+1 {
		runNode(id, addr, m.conf)
	}
	for {
		time.Sleep(time.Duration(IdleMs) * time.Millisecond)
	}
}

// runNode runs chain machine id at addr (cmd/node's main without flags and logging, over the
// in-memory store): its net/rpc server, and its announcement to the coordinator joinMs after the
// configuration arrived. It returns only if the server cannot listen.
func runNode(id uint64, addr string, conf Conf) {
	n := node.New(node.Opts{
		Address:           addr,
		CdrAddress:        ServerAddrs()[0],
		PubAddress:        addr,
		Store:             kv.New(),
		Transport:         netrpc.NewNodeClient,
		CoordinatorClient: netrpc.NewCoordinatorClient(),
	})
	nb := netrpc.NodeBinding{Svc: n}
	if err := rpc.RegisterName("RPC", &nb); err != nil {
		return
	}
	rpc.HandleHTTP()
	go func() {
		time.Sleep(time.Duration(joinMs(id, conf)) * time.Millisecond)
		n.Start()
	}()
	http.ListenAndServe(addr, nil)
}
