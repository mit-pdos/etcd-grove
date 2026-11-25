// Package swiftnet is the swiftpaxos kit (dsverify-lab's swift-n2nofast-1, notes/dsv-swiftpaxos.md)
// as an instance of examples/lib/remote: SwiftPaxos, one machine per node, each client on a machine
// of its own, its history checked by porcupine on an orchestrator machine. Thirteen machines, each
// a command of cmd/:
//
//   - the orchestrator (Orch, node 0): it chooses the configuration and the leader changes at
//     random and sends them to the nodes (New), then remote.Check of NC clients' K operations
//     each, made at the clients' own machines, against a key-value map with pending puts (Model);
//   - client machine c (Client, node 1+c): remote.ServeClient whose operation is a put or a get
//     through client c's own SwiftPaxos client (connected at its first operation);
//   - server machine id (Server, node NC+id, 1 <= id <= 1+MaxReplicas): the master (id 1) or a
//     replica (2 <= id <= N+1 of the configuration's N; the others only wait).
//
// The configuration is chosen at random by the orchestrator (New) and sent to every client node
// and to the server nodes that run (the master and the N replicas), which wait for it before they
// start (newClient, Server): 3 or 5 replicas, fast reads on or off (the configuration's optread),
// swift.New's pool level 0, 1 or 2, and swift.MaxDescRoutines 0, 2 or 100. The orchestrator also
// plans one or two leader changes, each made by a client node: after a random number of its
// client's returned operations, the client node asks a random replica to become the leader, as
// SwiftPaxos's master does when it suspects the leader (the replica's BeTheLeader over net/rpc).
//
// A call that fails, or a client that cannot connect, gives an unknown outcome (Out{Unknown:
// true}): a put of unknown outcome may have taken effect, may take effect later, or never.
//
// (dsverify-lab's kit ran its own Remote harness, with kitgen's generated Main and ClientNode, the
// lab's driver, recorder and check.KV over models.KvIn/KvOut; here they are remote's, lintest's
// and porcupine's, with the model below. The configuration and leader-change protocol, the
// server nodes' programs and the client's connection are the lab's, unchanged but for the
// addresses.)
package swiftnet

import (
	"fmt"
	"io"
	"log"
	"math/rand"
	"net"
	"net/http"
	"net/rpc"
	"strings"
	"sync"
	"time"

	"github.com/anishathalye/porcupine"
	"github.com/goose-lang/primitive"
	"github.com/imdea-software/swiftpaxos/client"
	"github.com/imdea-software/swiftpaxos/config"
	"github.com/imdea-software/swiftpaxos/dlog"
	"github.com/imdea-software/swiftpaxos/master"
	"github.com/imdea-software/swiftpaxos/replica/defs"
	"github.com/imdea-software/swiftpaxos/swift"
	"github.com/mit-pdos/etcd-grove/examples/lib/remote"
)

// The configuration: NC clients, K operations each, a remote call's limit CallMs, the most
// replicas, the keys, the port offsets of a node's rpc (a replica's net/rpc, a client node's
// request port), configuration and (a client node's) start addresses, the clients' start-up wait and stagger, the retry
// and idle waits (the lab's kit.toml).
const (
	NC          uint64 = 6
	K           uint64 = 8
	CallMs      uint64 = 30000
	MaxReplicas uint64 = 5
	NKeys       uint64 = 2
	RPCOff      uint64 = 1000
	ConfOff     uint64 = 2000
	StartOff    uint64 = 3000
	StartMs     uint64 = 15000
	StaggerMs   uint64 = 200
	RetryMs     uint64 = 100
	IdleMs      uint64 = 10000
)

// Addrs is every node's first address, by node id: node 0 is the orchestrator, nodes 1..NC the
// client nodes (client c on node 1+c), then the server nodes (server node id on node NC+id).
// All on loopback, so each node has its own ports (the lab gave each node its own host); the
// server nodes keep the lab's ports (the master's 7001, replica id's 7000+id, its net/rpc port
// RPCOff above, its configuration port ConfOff above), the client nodes 6101.., their request
// ports RPCOff above (ClientAddrs) and their configuration ports ConfOff above.
func Addrs() []string {
	return []string{
		"127.0.0.1:6100",
		"127.0.0.1:6101",
		"127.0.0.1:6102",
		"127.0.0.1:6103",
		"127.0.0.1:6104",
		"127.0.0.1:6105",
		"127.0.0.1:6106",
		"127.0.0.1:7001",
		"127.0.0.1:7002",
		"127.0.0.1:7003",
		"127.0.0.1:7004",
		"127.0.0.1:7005",
		"127.0.0.1:7006",
	}
}

// ClientAddrs is the client nodes' request addresses (client c's at index c: node 1+c's port
// RPCOff above its first), for the orchestrator's calls (remote.Serve).
func ClientAddrs() []string {
	return []string{
		"127.0.0.1:7101",
		"127.0.0.1:7102",
		"127.0.0.1:7103",
		"127.0.0.1:7104",
		"127.0.0.1:7105",
		"127.0.0.1:7106",
	}
}

// confAck is a node's answer to a configuration message it accepted.
const confAck = 0x6b

// MaxChanges is the most leader changes plan picks, and the most a message carries.
const MaxChanges = 2

// ConfLen is a configuration message's length in bytes (Conf.encode): the configuration's four
// bytes, the number of leader changes, and each change's Node and After.
const ConfLen = 5 + 2*MaxChanges

// Conf is a configuration of the deployment: the number of replicas and the replicas' options
// that vary (run.go's swift.New call has the others: exec on, optimistic execution on, AQreconf
// off, no slow addresses; no quorum file).
type Conf struct {
	N        uint64 // replicas: 3 or 5 (server nodes 2..N+1)
	FastRead uint64 // the configuration's optread (swift.New's fastRead): 0 or 1
	Pool     uint64 // swift.New's pl (descriptor pool from 1, fast-ack pool from 2): 0, 1 or 2
	Desc     uint64 // swift.MaxDescRoutines (run.go: 100): 0, 2 or 100
}

// change is a planned leader change: once After of client Client's operations have returned,
// client node Client asks server node Node (a replica) to become the leader.
type change struct {
	Client uint64
	Node   uint64
	After  uint64
}

// choose picks a configuration at random (math/rand: in the theorem, any choice).
func choose() Conf {
	n := uint64(3)
	if rand.Intn(2) == 1 {
		n = 5
	}
	descs := []uint64{0, 2, 100}
	return Conf{N: n, FastRead: uint64(rand.Intn(2)), Pool: uint64(rand.Intn(3)),
		Desc: descs[rand.Intn(3)]}
}

// plan picks one or two leader changes of the configuration conf at random: each made by a random
// client node, at a random replica (server nodes 2..N+1), once 1 to K-1 of that client's
// operations have returned (so that, in a test, the client still has operations to make).
func plan(conf Conf) []change {
	var cs []change
	n := 1 + rand.Intn(MaxChanges)
	for i := 0; i < n; i++ {
		cs = append(cs, change{Client: uint64(rand.Intn(int(NC))), Node: 2 + uint64(rand.Intn(int(conf.N))),
			After: 1 + uint64(rand.Intn(int(K-1)))})
	}
	return cs
}

// mine is the leader changes of cs that client c makes, in cs's order.
func mine(cs []change, c uint64) []change {
	var m []change
	for _, ch := range cs {
		if ch.Client == c {
			m = append(m, ch)
		}
	}
	return m
}

// encode is c with the leader changes cs (at most MaxChanges, all of one client) on the wire:
// ConfLen bytes, N, FastRead, Pool, Desc, the number of changes, then each change's Node and
// After (zero bytes for the ones missing).
func (c Conf) encode(cs []change) []byte {
	b := make([]byte, ConfLen)
	b[0] = byte(c.N)
	b[1] = byte(c.FastRead)
	b[2] = byte(c.Pool)
	b[3] = byte(c.Desc)
	b[4] = byte(len(cs))
	for i, ch := range cs {
		b[5+2*i] = byte(ch.Node)
		b[6+2*i] = byte(ch.After)
	}
	return b
}

// decode is the configuration and the leader changes b (ConfLen bytes) encodes, if b is a message
// configure can send (the changes' Client, which is not on the wire, is 0: a client node's are
// its own).
func decode(b []byte) (Conf, []change, bool) {
	c := Conf{N: uint64(b[0]), FastRead: uint64(b[1]), Pool: uint64(b[2]), Desc: uint64(b[3])}
	ok := (c.N == 3 || c.N == 5) && c.FastRead <= 1 && c.Pool <= 2 &&
		(c.Desc == 0 || c.Desc == 2 || c.Desc == 100) && uint64(b[4]) <= MaxChanges
	if !ok {
		return c, nil, false
	}
	var cs []change
	for i := uint64(0); i < uint64(b[4]); i++ {
		ch := change{Client: 0, Node: uint64(b[5+2*i]), After: uint64(b[6+2*i])}
		if ch.Node < 2 || ch.Node > c.N+1 || ch.After < 1 || ch.After >= K {
			return c, nil, false
		}
		cs = append(cs, ch)
	}
	return c, cs, true
}

// String is c for the log.
func (c Conf) String() string {
	return fmt.Sprintf("replicas %d, fast reads %d, pool level %d, max descriptor routines %d",
		c.N, c.FastRead, c.Pool, c.Desc)
}

// host is the host of the address addr ("host:port").
func host(addr string) string {
	return strings.Split(addr, ":")[0]
}

// port is the port of the address addr ("host:port"), its decimal digits read one by one.
func port(addr string) uint64 {
	p := strings.Split(addr, ":")[1]
	n := uint64(0)
	for i := 0; i < len(p); i++ {
		n = n*10 + uint64(p[i]-'0')
	}
	return n
}

// at is the address of node id's port off above its first (the deployment at addrs).
func at(addrs []string, id uint64, off uint64) string {
	return fmt.Sprintf("%s:%d", host(addrs[id]), port(addrs[id])+off)
}

// New is the orchestrator's setup of the deployment at addrs (node 0 the orchestrator, nodes
// 1..NC the client nodes, nodes NC+1..NC+1+MaxReplicas the server nodes): it chooses the
// configuration and the leader changes at random and sends them to every node that needs them.
func New(addrs []string) {
	conf := choose()
	configure(addrs, conf, plan(conf))
}

// configure sends the configuration conf to the master and replicas 2..conf.N+1 (server nodes,
// nodes NC+1..NC+1+conf.N) and to every client node, each with the leader changes of cs it makes,
// node n at its configuration address (its port ConfOff above its first), each until it
// acknowledges it; then, once every node has acknowledged its configuration, it sends the
// configuration again to every client node's start address (its port StartOff above its first),
// each until it acknowledges it. A client node connects its client only after the second message:
// SwiftPaxos's client may send commands only once every node of the deployment is set up (in the
// proof: every node registered its prediction, which the acknowledgments tell the orchestrator
// and the start message tells the client node).
func configure(addrs []string, conf Conf, cs []change) {
	log.Println("swiftnet: configuration: " + conf.String())
	for id := uint64(1); id <= conf.N+1; id++ {
		for !sendConf(at(addrs, NC+id, ConfOff), conf.encode(nil)) {
			time.Sleep(time.Duration(RetryMs) * time.Millisecond)
		}
	}
	for c := uint64(0); c < NC; c++ {
		for !sendConf(at(addrs, 1+c, ConfOff), conf.encode(mine(cs, c))) {
			time.Sleep(time.Duration(RetryMs) * time.Millisecond)
		}
	}
	for c := uint64(0); c < NC; c++ {
		for !sendConf(at(addrs, 1+c, StartOff), conf.encode(nil)) {
			time.Sleep(time.Duration(RetryMs) * time.Millisecond)
		}
	}
}

// sendConf sends the configuration message b to the node at addr and waits for its
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

// msg is a configuration message as a node decoded it.
type msg struct {
	conf Conf
	cs   []change
}

// awaitConf listens at addr (retrying a failed Listen), answers every valid configuration message
// it reads (the orchestrator sends again until it has an answer) and hands the first to ch. A
// connection that fails, or whose bytes are not a configuration message, is closed without an
// answer.
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
			if conf, cs, ok := decode(b[:]); ok {
				if first {
					ch <- msg{conf: conf, cs: cs}
					first = false
				}
				c.Write([]byte{confAck})
			}
		}
		c.Close()
	}
}

// Sys is a client node's view of the deployment: the addresses, the configuration, its one
// SwiftPaxos client (nil: not connected), the number of the client's operations that have
// returned (mu guards it), and the number of operations op has started (opMu guards it and the
// client: remote.Serve runs one operation at a time, but remote.ServeClient's contract lets its
// newClient hand the same system to any number of callers, so op locks).
type Sys struct {
	addrs []string
	conf  Conf
	b     *client.BufferClient
	mu    sync.Mutex
	done  uint64
	opMu  sync.Mutex
	ops   uint64
}

// MaxOps bounds a client's operations: an operation past it answers unknown without sending
// anything. A SwiftPaxos client numbers its commands by sequence numbers, and the proof bounds a
// client's below 2^10 (the size of a replica's gob-encoded MSync, which carries every client's
// commands, must fit gob's message limit). The orchestrator makes K operations per client;
// remote.ServeClient's contract allows any number.
const MaxOps uint64 = 1000

// MaxVal bounds a put's value: a longer one answers unknown without sending anything (a
// SwiftPaxos command's value travels with a 16-bit length on the client's wire, and the proof's
// spec of BufferClient.Write takes values below 2^16; the orchestrator's are a few bytes).
const MaxVal uint64 = 1 << 16

// newClient is client c's node's side of the deployment at addrs: it waits for the
// configuration on client node c's configuration address (node 1+c, port ConfOff above its
// first), then for the start message on its start address (port StartOff above its first: every
// node is configured), registers the net/rpc codec (the model's; nothing in the real build) and starts the
// leader changes this node makes; client c's SwiftPaxos client connects at its first operation
// (op).
func newClient(addrs []string, c uint64) *Sys {
	ch := make(chan msg, 1)
	go awaitConf(at(addrs, 1+c, ConfOff), ch)
	m := <-ch
	st := make(chan msg, 1)
	go awaitConf(at(addrs, 1+c, StartOff), st)
	<-st
	Register()
	s := &Sys{addrs: addrs, conf: m.conf}
	go s.changeLeaders(m.cs)
	return s
}

// returned counts an operation of the client that returned.
func (s *Sys) returned() {
	s.mu.Lock()
	s.done++
	s.mu.Unlock()
}

// changeLeaders makes the leader changes cs: once each one's number of the client's operations
// have returned, it asks the replica to become the leader as SwiftPaxos's master does when it
// suspects the leader (the replica's BeTheLeader, over net/rpc at its rpc port, server node
// Node's port RPCOff above its first); a failed call is not retried.
func (s *Sys) changeLeaders(cs []change) {
	for _, ch := range cs {
		for {
			s.mu.Lock()
			d := s.done
			s.mu.Unlock()
			if d >= ch.After {
				break
			}
			time.Sleep(time.Duration(RetryMs) * time.Millisecond)
		}
		log.Printf("swiftnet: leader change: server node %d after %d operations", ch.Node, ch.After)
		cli, err := rpc.DialHTTP("tcp", at(s.addrs, NC+ch.Node, RPCOff))
		if err == nil {
			cli.Call("Replica.BeTheLeader", &defs.BeTheLeaderArgs{}, defs.NewBeTheLeaderReply())
			cli.Close()
		}
	}
}

// connect connects client c as SwiftPaxos's client program does for SwiftPaxos (main.go's
// runSingleClient: client.NewClientLog, NewBufferClient, Connect, swift.NewClient): to the
// master (server node 1, node NC+1), then to every replica the master lists as alive, after a
// random stagger (0 to NC*StaggerMs). The client's id is c + 1 instead of NewClientLog's random
// one (a uuid's ID: the protocol needs distinct ids, which a uuid gives only with high
// probability). true if connected.
func (s *Sys) connect(c uint64) bool {
	time.Sleep(time.Duration(rand.Intn(int(NC*StaggerMs)+1)) * time.Millisecond)
	m := s.addrs[NC+1]
	cli := client.NewClientLog("", host(m), int(port(m)), true, false, false, &dlog.Logger{})
	cli.ClientId = int32(c) + 1
	b := client.NewBufferClient(cli, int(K), 0, 0, 0, 0)
	if err := b.Connect(); err != nil {
		b.Disconnect()
		return false
	}
	swift.NewClient(b, int(s.conf.N))
	s.b = b
	return true
}

// In is an operation of the key-value map: a put of V at key K (Put), or a get of key K. Keys
// are 0..NKeys-1 (SwiftPaxos's state.Key K).
type In struct {
	Put bool
	K   uint64
	V   string
}

// Out is an operation's output: a get's value ("": not found; puts never write ""), "" for a
// put, or Unknown (the operation's outcome is unknown).
type Out struct {
	Unknown bool
	V       string
}

// op is client c's operation on client node c (one at a time, at most MaxOps), through its
// SwiftPaxos client (newClient's Sys, connected at the client's first operation): a put is BufferClient.Write, a get
// BufferClient.Read. Both wait for the client's reply (the SwiftPaxos client's fast or slow
// quorum, or an accept); a client that cannot connect gives an unknown outcome and tries again at
// its next operation.
func op(s *Sys, c uint64, in In) Out {
	s.opMu.Lock()
	out := op1(s, c, in)
	s.opMu.Unlock()
	return out
}

// op1 is op's body, run with s.opMu held: past MaxOps operations, or for a value of MaxVal
// bytes or more, an unknown outcome.
func op1(s *Sys, c uint64, in In) Out {
	if s.ops >= MaxOps || uint64(len(in.V)) >= MaxVal {
		return Out{Unknown: true}
	}
	s.ops++
	if s.b == nil && !s.connect(c) {
		return Out{Unknown: true}
	}
	if in.Put {
		s.b.Write(int64(in.K), []byte(in.V))
		s.returned()
		return Out{}
	}
	v := s.b.Read(int64(in.K))
	s.returned()
	return Out{V: string(v)}
}

// digits is n in decimal.
func digits(n uint64) string {
	if n < 10 {
		return string([]byte{byte('0' + n)})
	}
	return digits(n/10) + digits(n%10)
}

// Gen is a client's input, at random: a put (one in two) or a get of one of the NKeys keys, a
// put's value one of "v0".."v999" (never empty).
func Gen(c int) any {
	n := primitive.RandomUint64()
	k := n % NKeys
	if (n/NKeys)%2 == 0 {
		return In{Put: true, K: k, V: "v" + digits((n/(2*NKeys))%1000)}
	}
	return In{Put: false, K: k, V: ""}
}

// State is the model's state: per key k, its value Cur[k] ("": none) and the puts of unknown
// outcome at k, Pend[k] (each may still take effect, once, or never). It stands for the
// configurations whose value at k is Cur[k] with any of Pend[k] still pending, or is a value x of
// Pend[k] (taken effect) with any of the others still pending. States are never written.
type State struct {
	Cur  []string
	Pend [][]string
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

// push is p with v added, in a new slice.
func push(p []string, v string) []string {
	q := make([]string, len(p)+1)
	copy(q, p)
	q[len(p)] = v
	return q
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

// setCur is c with c[k] = v, in a new slice.
func setCur(c []string, k uint64, v string) []string {
	d := make([]string, len(c))
	copy(d, c)
	d[k] = v
	return d
}

// setPend is p with p[k] = q, in a new slice.
func setPend(p [][]string, k uint64, q []string) [][]string {
	d := make([][]string, len(p))
	copy(d, p)
	d[k] = q
	return d
}

// step is the model's step: a put of unknown outcome is pending; a get of unknown outcome says
// nothing; an answered put sets its key; an answered get of k that returned v is one at a
// configuration where k's value is v (Cur[k], or a pending put of v taking effect first).
func step(s State, in In, o Out) (bool, State) {
	if o.Unknown {
		if in.Put {
			return true, State{Cur: s.Cur, Pend: setPend(s.Pend, in.K, push(s.Pend[in.K], in.V))}
		}
		return true, s
	}
	if in.Put {
		return o.V == "", State{Cur: setCur(s.Cur, in.K, in.V), Pend: s.Pend}
	}
	if o.V == s.Cur[in.K] {
		return true, s
	}
	if has(s.Pend[in.K], o.V) {
		return true, State{Cur: setCur(s.Cur, in.K, o.V),
			Pend: setPend(s.Pend, in.K, erase(s.Pend[in.K], o.V))}
	}
	return false, s
}

// initState is the map with no key set and nothing pending.
func initState() State {
	return State{Cur: make([]string, NKeys), Pend: make([][]string, NKeys)}
}

// Model is the key-value map with pending puts (linkv's pending-writes store), as a porcupine
// model. Inputs are Ins, outputs Outs.
func Model() porcupine.Model {
	return porcupine.Model{
		Init: func() any { return initState() },
		Step: func(state, input, output any) (bool, any) {
			ok, s := step(state.(State), input.(In), output.(Out))
			return ok, s
		},
		// Equal is always false: two histories can reach the same State whose sets of
		// configurations differ (put a unknown then put b, or the other order: only the first
		// allows a having taken effect before b), so a State does not determine the set porcupine's
		// Equal must compare (dsv-epaxos's finding); false is sound and only costs caching.
		Equal: func(a, b any) bool { return false },
	}
}

// Codec is the map's codec: an input as a byte (1: a put), the key's byte and the value's bytes;
// an output as a byte (1: unknown) and the value's bytes. A get is a read.
func Codec() remote.Codec {
	return remote.Codec{
		EncIn: func(in any) []byte {
			i := in.(In)
			b := make([]byte, 2, 2+len(i.V))
			if i.Put {
				b[0] = 1
			}
			b[1] = byte(i.K)
			return append(b, []byte(i.V)...)
		},
		DecIn: func(b []byte) (any, bool) {
			if len(b) < 2 || b[0] > 1 || uint64(b[1]) >= NKeys {
				return nil, false
			}
			return In{Put: b[0] == 1, K: uint64(b[1]), V: string(b[2:])}, true
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
		IsRead:    func(in any) bool { return !in.(In).Put },
		Unknown:   func(in any) any { return Out{Unknown: true} },
		IsUnknown: func(out any) bool { return out.(Out).Unknown },
	}
}

// callTime is CallMs as a duration.
func callTime() time.Duration {
	return time.Duration(CallMs) * time.Millisecond
}

// Orch is the orchestrator's program: it configures the deployment (New), waits StartMs for the
// master, the replicas and the client nodes to start, draws each client's number of operations,
// 1 to K, then panics unless porcupine accepts the history of the clients' operations.
func Orch() {
	orch(Addrs(), ClientAddrs())
}

// orch is Orch in the deployment at addrs with client request addresses caddrs.
func orch(addrs []string, caddrs []string) {
	New(addrs)
	time.Sleep(time.Duration(StartMs) * time.Millisecond)
	remote.Check(Model(), caddrs, Codec(), Gen, 1+rand.Intn(int(K)), callTime())
}

// Client is client machine c's program (c < NC): its own client node of the deployment, made
// once, before serving (remote.ServeClient's newClient may be called any number of times as far
// as its contract says, and client c's node waits for the configuration and starts its leader
// changes once), served at its address in ClientAddrs. It never returns.
func Client(c uint64) {
	clientNode(Addrs(), ClientAddrs()[c], c)
}

// clientNode is Client in the deployment at addrs, serving at caddr.
func clientNode(addrs []string, caddr string, c uint64) {
	s := newClient(addrs, c)
	newC := func(id int) any {
		return s
	}
	opC := func(sys any, in any) any {
		return op(sys.(*Sys), c, in.(In))
	}
	remote.ServeClient(int(c), caddr, newC, opC, Codec(), callTime())
}

// Server is server node id's program (id 1..1+MaxReplicas, node NC+id): id 1 is the master, ids
// 2.. SwiftPaxos's replicas (main.go's runMaster and run.go's runReplica, with the configuration
// built here instead of read from files), once the orchestrator has sent the configuration. It
// never returns.
func Server(id uint64) {
	serve(id, Addrs())
}

// nodeConfig is server node id's configuration as SwiftPaxos's config.Read gives it for a config
// file with no proxies and no leader, fast reads as conf says and the deployment's addresses being
// the kit's (no quorum, latency or log file: defs.LatencyConf stays "").
func nodeConfig(id uint64, port int, conf Conf) *config.Config {
	return &config.Config{
		Protocol: "swiftpaxos",
		Alias:    "n" + digits(id),
		Port:     port,
		Optread:  conf.FastRead == 1,
		Fast:     true,
		Leader:   nil,
		Quorum:   "",
		Proxy:    &config.ProxyInfo{},
	}
}

// register is runReplica's registerWithMaster: it registers (ip, port) with the master at maddr
// until the master says it is ready, and returns the replica's id and the replicas' addresses.
// Unlike runReplica's, it dials again after a failed call (runReplica retries the same client,
// which fails forever once its connection broke) and waits RetryMs between calls (runReplica
// 4 ns).
func register(ip string, port int, maddr string) (int, []string) {
	args := &defs.RegisterArgs{Addr: ip, Port: port}
	for {
		mcli, err := rpc.DialHTTP("tcp", maddr)
		if err == nil {
			for {
				var reply defs.RegisterReply
				if err := mcli.Call("Master.Register", args, &reply); err != nil {
					break
				}
				if reply.Ready {
					mcli.Close()
					return reply.ReplicaId, reply.NodeList
				}
				time.Sleep(time.Duration(RetryMs) * time.Millisecond)
			}
			mcli.Close()
		}
		time.Sleep(time.Duration(RetryMs) * time.Millisecond)
	}
}

// serve is server node id's program in the deployment at addrs (Server's; kit_test.go's on
// loopback): it waits for the configuration (on node NC+id's port ConfOff above its first), then
// runs the master (id 1) or, if id - 2 < N, replica id. The logger is SwiftPaxos's non-verbose
// dlog.Logger (dlog.New(path, false) less the log file it never writes): no output, and its Fatal
// does not exit.
func serve(id uint64, addrs []string) {
	ch := make(chan msg, 1)
	go awaitConf(at(addrs, NC+id, ConfOff), ch)
	conf := (<-ch).conf
	Register()
	p := int(port(addrs[NC+id]))
	cfg := nodeConfig(id, p, conf)
	if id == 1 {
		m := master.New(int(conf.N), p, cfg, &dlog.Logger{})
		m.Run()
		return
	}
	if id-2 < conf.N {
		ip := host(addrs[NC+id])
		replicaId, nodeList := register(ip, p, addrs[NC+1])
		swift.MaxDescRoutines = int(conf.Desc)
		rep := swift.New(cfg.Alias, replicaId, nodeList, true, conf.FastRead == 1, true, false,
			int(conf.Pool), int((conf.N-1)/2), cfg, &dlog.Logger{}, nil)
		if err := rpc.Register(rep); err == nil {
			rpc.HandleHTTP()
			l, err := net.Listen("tcp", at(addrs, NC+id, RPCOff))
			if err == nil {
				http.Serve(l, nil)
			}
		}
	}
	for {
		time.Sleep(time.Duration(IdleMs) * time.Millisecond)
	}
}
