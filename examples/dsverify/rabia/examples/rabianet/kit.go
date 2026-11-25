// Package rabianet is the rabia kit (dsverify-lab's rabia-r1wake-1, notes/dsv-rabia.md) as an
// instance of examples/lib/remote: Rabia's replicated key-value store, one process per machine,
// each client on a machine of its own, checked by porcupine on an orchestrator machine. Twelve
// machines, each a command of cmd/:
//
//   - the orchestrator (Orch): chooses the configuration at random and sends it to every client
//     machine and to the server machines that run Rabia servers (New), waits StartMs, then
//     remote.Check of NC clients' K operations each, made at the clients' own machines, against
//     the key-value map with pending puts (Model);
//   - client machine c (Client, c < NC): waits for the configuration, configures Rabia, connects
//     Rabia client endpoint c to the proxy of server c mod N, then remote.ServeClient whose
//     operation is one request on that endpoint (Op);
//   - server machine id (Server, 1 <= id <= MaxServers): waits for the configuration and, if id is
//     one of its N servers, runs Rabia server id-1; else only waits.
//
// The configuration: 3 or 5 servers with f = 1, or 2 of 5, faulty; the proxies' batch size and
// batch timeout; the length of a ledger slot's per-phase arrays.
//
// A put whose call fails, or that gets no reply within OpMs, has an unknown outcome
// (Out{Unknown: true}): it may have taken effect, may take effect later, or never. A get whose
// calls fail answers unknown too, and constrains nothing.
//
// (dsverify-lab's kit ran on its own Remote harness with the lab's recorder and key-value checker
// and its porcupine axiom; here they are remote's, lintest's and the verified porcupine. Its
// configuration hand-off and Rabia's code are the lab's.)
package rabianet

import (
	"io"
	"log"
	"math/rand"
	"net"
	"sync"
	"sync/atomic"
	"time"

	"github.com/anishathalye/porcupine"
	"github.com/mit-pdos/etcd-grove/examples/lib/remote"
	"rabia/internal/config"
	"rabia/internal/message"
	"rabia/internal/tcp"
	"rabia/roles/server"
)

// The configuration of the test: NC clients, K operations each, MaxServers server machines,
// NKeys keys of KeyLen bytes, how long an operation waits for Rabia's reply (OpMs), how long a
// failed Listen or an unacknowledged configuration waits before it is tried again (RetryMs), how
// long the orchestrator waits after the configuration before the clients' first operations
// (StartMs: the servers connect to one another before their proxies accept clients).
const (
	NC         uint64 = 6
	K          uint64 = 8
	MaxServers uint64 = 5
	NKeys      uint64 = 2
	KeyLen     uint64 = 8
	OpMs       uint64 = 8000
	RetryMs    uint64 = 100
	StartMs    uint64 = 3000
)

// AttemptMs bounds one call between the orchestrator and a client machine: longer than an
// operation's wait (OpMs).
const AttemptMs uint64 = 12000

// ProjectFolder is Rabia's Conf.ProjectFolder (its logger's directory; the kit's logger writes
// nothing).
const ProjectFolder = "/tmp/rabia-net"

// ProxyAddrs is the server machines' proxy addresses (server machine id at index id-1), where
// clients connect.
func ProxyAddrs() []string {
	return []string{
		"127.0.0.1:7601",
		"127.0.0.1:7602",
		"127.0.0.1:7603",
		"127.0.0.1:7604",
		"127.0.0.1:7605",
	}
}

// NetAddrs is the server machines' network-layer addresses (Conf.Peers: server machine id at index
// id-1), where the servers connect to one another.
func NetAddrs() []string {
	return []string{
		"127.0.0.1:7611",
		"127.0.0.1:7612",
		"127.0.0.1:7613",
		"127.0.0.1:7614",
		"127.0.0.1:7615",
	}
}

// ServerConfAddrs is the server machines' configuration addresses (server machine id at index
// id-1), where they wait for the configuration.
func ServerConfAddrs() []string {
	return []string{
		"127.0.0.1:7621",
		"127.0.0.1:7622",
		"127.0.0.1:7623",
		"127.0.0.1:7624",
		"127.0.0.1:7625",
	}
}

// ClientAddrs is the client machines' addresses for the orchestrator's calls (remote.Serve).
func ClientAddrs() []string {
	return []string{
		"127.0.0.1:7631",
		"127.0.0.1:7632",
		"127.0.0.1:7633",
		"127.0.0.1:7634",
		"127.0.0.1:7635",
		"127.0.0.1:7636",
	}
}

// ClientConfAddrs is the client machines' configuration addresses.
func ClientConfAddrs() []string {
	return []string{
		"127.0.0.1:7641",
		"127.0.0.1:7642",
		"127.0.0.1:7643",
		"127.0.0.1:7644",
		"127.0.0.1:7645",
		"127.0.0.1:7646",
	}
}

// confAck is a machine's answer to a configuration it accepted.
const confAck = 0x6b

// confLen is the length of a configuration on the wire (encode).
const confLen = 5

// Conf is a configuration of the deployment: Rabia's NServers and NFaulty, and the positions of
// its ProxyBatchSize, ProxyBatchTimeout and LenBlockArray in batchSize's, batchMs's and blocks's
// lists.
type Conf struct {
	N       uint64 // servers: 3 or 5, on server machines 1..N, Rabia server ids 0..N-1 (Conf.NServers)
	F       uint64 // faulty servers tolerated: 1 <= F <= (N-1)/2 (Conf.NFaulty)
	Batch   uint64 // a proxy's batch: up to batchSize(Batch) client requests (Conf.ProxyBatchSize)
	BatchMs uint64 // a proxy's batch timeout: batchMs(BatchMs) ms (Conf.ProxyBatchTimeout)
	Blocks  uint64 // a ledger slot's per-phase arrays: blocks(Blocks) phases (Conf.LenBlockArray)
}

// NBatches, NBatchMs and NBlocks are the number of batch sizes, batch timeouts and per-phase array
// lengths choose picks from.
const NBatches = 4
const NBatchMs = 5
const NBlocks = 4

// batchSize is the i-th proxy batch size (i < NBatches): 1, 2, 3, 10 client requests. A proxy
// sends a batch when it is full or when its batch timeout fires with requests pending.
func batchSize(i uint64) uint64 {
	return []uint64{1, 2, 3, 10}[i]
}

// batchMs is the i-th proxy batch timeout, in ms (i < NBatchMs): 1, 2, 5, 10, 50. Time is not
// modeled, so in the theorem the values do not matter; in a test, they decide which requests a
// batch holds.
func batchMs(i uint64) uint64 {
	return []uint64{1, 2, 5, 10, 50}[i]
}

// blocks is the i-th length of a ledger slot's per-phase arrays (i < NBlocks): 2, 3, 5 or 10 (the
// last is CalcConstants'). Phase 0 and the first coin phase need 2; a slot that runs more phases
// than the arrays hold uses entries past their end.
func blocks(i uint64) uint64 {
	return []uint64{2, 3, 5, 10}[i]
}

// choose picks a configuration at random (math/rand: in the theorem, any choice).
func choose() Conf {
	n := uint64(3)
	f := uint64(1)
	s := rand.Intn(3)
	if s == 1 {
		n = 5
	}
	if s == 2 {
		n = 5
		f = 2
	}
	return Conf{N: n, F: f, Batch: uint64(rand.Intn(NBatches)), BatchMs: uint64(rand.Intn(NBatchMs)),
		Blocks: uint64(rand.Intn(NBlocks))}
}

// encode is c on the wire: five bytes, N, F, Batch, BatchMs and Blocks.
func (c Conf) encode() []byte {
	return []byte{byte(c.N), byte(c.F), byte(c.Batch), byte(c.BatchMs), byte(c.Blocks)}
}

// decode is the configuration b (confLen bytes) encodes, if b is one choose can pick.
func decode(b []byte) (Conf, bool) {
	c := Conf{N: uint64(b[0]), F: uint64(b[1]), Batch: uint64(b[2]), BatchMs: uint64(b[3]), Blocks: uint64(b[4])}
	return c, (c.N == 3 || c.N == 5) && 1 <= c.F && 2*c.F < c.N && c.Batch < NBatches && c.BatchMs < NBatchMs &&
		c.Blocks < NBlocks
}

// String is c for the log: "servers N, f F, batch B, batch timeout T ms, phase arrays L".
func (c Conf) String() string {
	return "servers " + digits(c.N) + ", f " + digits(c.F) + ", batch " + digits(batchSize(c.Batch)) +
		", batch timeout " + digits(batchMs(c.BatchMs)) + " ms, phase arrays " + digits(blocks(c.Blocks))
}

// configure sets Rabia's global configuration Conf as main.go's Conf.LoadConfigs does from the
// environment (a server's or a client's variables), for the kit's deployment in configuration
// conf: conf.N servers, conf.F of them faulty, NC clients, a proxy batch of up to
// batchSize(conf.Batch) client requests of one command each, sent after batchMs(conf.BatchMs) ms,
// the in-memory store, peers at peers; then Rabia's own CalcConstants (the ledger's length
// LenLedger = 10000, channel and buffer sizes, 8-byte keys), the per-slot phase arrays'
// length blocks(conf.Blocks) in place of CalcConstants' 10, and loadRedisVars' StorageMode 0.
func configure(peers []string, conf Conf) {
	c := &config.Conf
	c.Role = "svr"
	c.LogLevel = "warn"
	c.ProjectFolder = ProjectFolder
	c.Peers = peers
	c.ClosedLoop = true
	c.NServers = int(conf.N)
	c.NFaulty = int(conf.F)
	c.NClients = int(NC)
	c.NConcurrency = 1
	c.ProxyBatchSize = int(batchSize(conf.Batch))
	c.ProxyBatchTimeout = time.Duration(batchMs(conf.BatchMs)) * time.Millisecond
	c.NetworkBatchSize = 0
	c.NetworkBatchTimeout = 0
	c.ClientBatchSize = 1
	c.ClientTimeout = 0
	c.ClientThinkTime = 0
	c.NClientRequests = int(K)
	c.CalcConstants()
	c.LenBlockArray = int(blocks(conf.Blocks))
	c.StorageMode = 0
}

// sendConf sends the configuration b to the machine at addr and waits for its acknowledgment; true
// if acknowledged.
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

// send sends the configuration conf to every client machine and to server machines 1..conf.N, at
// their configuration addresses, each until it acknowledges it.
func send(conf Conf) {
	log.Println("rabianet: configuration: " + conf.String())
	for c := uint64(0); c < NC; c++ {
		for !sendConf(ClientConfAddrs()[c], conf.encode()) {
			time.Sleep(time.Duration(RetryMs) * time.Millisecond)
		}
	}
	for id := uint64(1); id <= conf.N; id++ {
		for !sendConf(ServerConfAddrs()[id-1], conf.encode()) {
			time.Sleep(time.Duration(RetryMs) * time.Millisecond)
		}
	}
}

// New is the orchestrator's setup of the deployment: it chooses the configuration at random and
// sends it to every machine that needs it.
func New() {
	send(choose())
}

// awaitConf listens on addr (retrying a failed Listen) and answers every configuration it reads
// with an acknowledgment (the orchestrator sends again until it has one); the first is sent on ch.
// A connection that fails, or whose bytes are not a configuration, is closed without an answer.
func awaitConf(addr string, ch chan Conf) {
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
		var b [confLen]byte
		if _, err := io.ReadFull(c, b[:]); err == nil {
			if conf, ok := decode(b[:]); ok {
				if first {
					ch <- conf
					first = false
				}
				c.Write([]byte{confAck})
			}
		}
		c.Close()
	}
}

// waitConf is the configuration the orchestrator sends to the machine whose configuration
// address is addr (awaitConf, which goes on answering).
func waitConf(addr string) Conf {
	ch := make(chan Conf, 1)
	go awaitConf(addr, ch)
	return <-ch
}

// In is an operation of the key-value map: a put of V at K (Put), or a get of K.
type In struct {
	Put bool
	K   string
	V   string
}

// Out is an operation's output: a put's (Put), a get's (Found, and the value V if found), or
// Unknown (the operation's outcome is unknown).
type Out struct {
	Unknown bool
	Put     bool
	Found   bool
	V       string
}

// Entry is one key's state in the model: its value (Cur; "" if never written, as Gen's values
// are never empty) and the values of its puts of unknown outcome that have not been seen, each of
// which may still take effect, once, or never: those made since Cur was set (Pend: if one has
// taken effect, the key's value is no longer Cur) and those made before (Old: one may have taken
// effect before Cur was set, and been overwritten). The split makes the state stand for exactly
// the configurations the history allows (two histories with the same entries allow the same
// configurations), as Equal needs.
type Entry struct {
	K    string
	Cur  string
	Old  []string
	Pend []string
}

// State is the model's state: the keys' entries (a key with none: Cur "" and nothing pending).
// With distinct put values it stands for exactly the configurations the history allows.
type State struct {
	Es []Entry
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

// cat is a followed by b, in a new slice.
func cat(a []string, b []string) []string {
	q := make([]string, len(a)+len(b))
	copy(q, a)
	copy(q[len(a):], b)
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

// find is k's entry in s (an empty one if s has none).
func find(s State, k string) Entry {
	for i := 0; i < len(s.Es); i++ {
		if s.Es[i].K == k {
			return s.Es[i]
		}
	}
	return Entry{K: k}
}

// set is s with k's entry e, in a new slice.
func set(s State, e Entry) State {
	es := make([]Entry, 0, len(s.Es)+1)
	found := false
	for i := 0; i < len(s.Es); i++ {
		if s.Es[i].K == e.K {
			es = append(es, e)
			found = true
		} else {
			es = append(es, s.Es[i])
		}
	}
	if !found {
		es = append(es, e)
	}
	return State{Es: es}
}

// step is the model's step: a put of unknown outcome is pending; an answered put sets its key's
// value (the pending puts become old); an answered get of v is one at a configuration where v is
// the key's value (already, or by a pending put of v taking effect first: then the other pending
// puts become old); a get of unknown outcome changes nothing.
func step(s State, in In, o Out) (bool, State) {
	e := find(s, in.K)
	if o.Unknown {
		if in.Put {
			return true, set(s, Entry{K: in.K, Cur: e.Cur, Old: e.Old, Pend: push(e.Pend, in.V)})
		}
		return true, s
	}
	if in.Put {
		return o.Put, set(s, Entry{K: in.K, Cur: in.V, Old: cat(e.Old, e.Pend), Pend: nil})
	}
	if o.Put {
		return false, s
	}
	v := ""
	if o.Found {
		v = o.V
	}
	if v == e.Cur {
		return true, s
	}
	all := cat(e.Old, e.Pend)
	if v != "" && has(all, v) {
		return true, set(s, Entry{K: in.K, Cur: v, Old: erase(all, v), Pend: nil})
	}
	return false, s
}

// equalStrs reports whether a and b are the same list.
func equalStrs(a []string, b []string) bool {
	if len(a) != len(b) {
		return false
	}
	for i := 0; i < len(a); i++ {
		if a[i] != b[i] {
			return false
		}
	}
	return true
}

// equal reports whether a and b are the same state (as values: the same entries in the same
// order).
func equal(a State, b State) bool {
	if len(a.Es) != len(b.Es) {
		return false
	}
	for i := 0; i < len(a.Es); i++ {
		if a.Es[i].K != b.Es[i].K || a.Es[i].Cur != b.Es[i].Cur || !equalStrs(a.Es[i].Old, b.Es[i].Old) ||
			!equalStrs(a.Es[i].Pend, b.Es[i].Pend) {
			return false
		}
	}
	return true
}

// Model is the key-value map with pending puts, as a porcupine model. Inputs are Ins, outputs
// Outs.
func Model() porcupine.Model {
	return porcupine.Model{
		Init: func() any { return State{} },
		Step: func(state, input, output any) (bool, any) {
			ok, s := step(state.(State), input.(In), output.(Out))
			return ok, s
		},
		Equal: func(a, b any) bool { return equal(a.(State), b.(State)) },
	}
}

// Codec is the map's codec: an input as a byte (1: a put), the key's length in 8 bytes, the key,
// the value; an output as a byte (0: a get not found, 1: found, 2: a put's, 3: unknown) and the
// value.
func Codec() remote.Codec {
	return remote.Codec{
		EncIn: func(in any) []byte {
			x := in.(In)
			b := make([]byte, 9, 9+len(x.K)+len(x.V))
			if x.Put {
				b[0] = 1
			}
			putU64(b[1:], uint64(len(x.K)))
			b = append(b, []byte(x.K)...)
			return append(b, []byte(x.V)...)
		},
		DecIn: func(b []byte) (any, bool) {
			if len(b) < 9 || b[0] > 1 {
				return nil, false
			}
			n := getU64(b[1:])
			if n > uint64(len(b)-9) {
				return nil, false
			}
			return In{Put: b[0] == 1, K: string(b[9 : 9+n]), V: string(b[9+n:])}, true
		},
		EncOut: func(out any) []byte {
			o := out.(Out)
			b := make([]byte, 1, 1+len(o.V))
			if o.Unknown {
				b[0] = 3
			} else if o.Put {
				b[0] = 2
			} else if o.Found {
				b[0] = 1
			}
			return append(b, []byte(o.V)...)
		},
		DecOut: func(b []byte) (any, bool) {
			if len(b) < 1 || b[0] > 3 {
				return nil, false
			}
			return Out{Unknown: b[0] == 3, Put: b[0] == 2, Found: b[0] == 1, V: string(b[1:])}, true
		},
		IsRead:    func(in any) bool { return !in.(In).Put },
		Unknown:   func(in any) any { return Out{Unknown: true} },
		IsUnknown: func(out any) bool { return out.(Out).Unknown },
	}
}

// putU64 writes x into b's first 8 bytes, little-endian.
func putU64(b []byte, x uint64) {
	for i := uint64(0); i < 8; i++ {
		b[i] = byte(x >> (8 * i))
	}
}

// getU64 is b's first 8 bytes, little-endian.
func getU64(b []byte) uint64 {
	x := uint64(0)
	for i := uint64(0); i < 8; i++ {
		x = x | (uint64(b[i]) << (8 * i))
	}
	return x
}

// mix is a fixed hash of client c's round r (multiply-xorshift, wrapping uint64 arithmetic): Gen's
// key for the round is mix(c, r) mod NKeys, so the rounds spread over the keys (TestGen checks it
// for NC and K) without a fixed per-client pattern of the keys' order and without state.
func mix(c uint64, r uint64) uint64 {
	x := c*0x9E3779B97F4A7C15 + r*0xBF58476D1CE4E5B9 + 1
	x ^= x >> 31
	x *= 0x94D049BB133111EB
	x ^= x >> 29
	return x
}

// digit is n's last decimal digit.
func digit(n uint64) string {
	return string([]byte{byte('0' + n%10)})
}

// digits is n in decimal.
func digits(n uint64) string {
	if n < 10 {
		return digit(n)
	}
	return digits(n/10) + digit(n)
}

// Gen is client c's j-th input: a put (j even) and then a get (j odd) of the same key, round j/2's
// key "key0000<mix(c, j/2) mod NKeys>" (KeyLen, 8 bytes; the get reads the key its own put wrote,
// and every key is written and read by several clients); put values "v<c><j>" are distinct and
// never empty (c and j below 10).
func Gen(c uint64, j uint64) In {
	k := "key0000" + digit(mix(c, j/2)%NKeys)
	if j%2 == 0 {
		return In{Put: true, K: k, V: "v" + digit(c) + digit(j)}
	}
	return In{Put: false, K: k, V: ""}
}

// gens is remote's generator over Gen: client c's next input (lintest's generator is given the
// client only; each client's count of the inputs it was given is its own atomic counter). A
// client index outside the deployment's (which remote.Check never passes) gets its first input.
func gens() func(int) any {
	next := make([]uint64, NC)
	return func(c int) any {
		if c < 0 || uint64(c) >= NC {
			return Gen(uint64(c), 0)
		}
		j := atomic.AddUint64(&next[c], 1) - 1
		return Gen(uint64(c), j)
	}
}

// attempt is AttemptMs as a duration.
func attempt() time.Duration {
	return time.Duration(AttemptMs) * time.Millisecond
}

// Orch is the orchestrator's program: it sends the configuration (New), waits a random 0 to
// StartMs, draws each client's number of operations, 1 to K, and panics unless porcupine accepts
// the history of the clients' operations.
func Orch() {
	New()
	time.Sleep(time.Duration(rand.Intn(int(StartMs)+1)) * time.Millisecond)
	remote.Check(Model(), ClientAddrs(), Codec(), gens(), 1+rand.Intn(int(K)), attempt())
}

// Sys is a client machine's view of the deployment: the configuration, its one Rabia client
// endpoint (internal/tcp's ClientTCP: one connection to its proxy, kept for all of the client's
// operations, as Rabia's client keeps it) and the sequence number of its next request, which mu
// guards (remote.Serve runs one operation at a time, but remote.ServeClient's contract lets its
// newClient hand the same system to any number of callers, so Op locks: notes/dsv-rabia.md).
type Sys struct {
	conf Conf
	t    *tcp.ClientTCP
	mu   *sync.Mutex
	next uint32
}

// newClient is client c's side of the deployment: it waits for the configuration, configures
// Rabia's Conf from it (as the servers do) and connects client c, with Rabia client id c, to the
// proxy of server c mod N (Rabia's "modulo" distribution), through ClientTcpInit and Connect
// (which dials until it connects, sends the handshake and starts the endpoint's send and receive
// routines).
func newClient(c uint64) *Sys {
	conf := waitConf(ClientConfAddrs()[c])
	configure(NetAddrs()[:conf.N], conf)
	t := tcp.ClientTcpInit(uint32(c), ProxyAddrs()[c%conf.N])
	t.Connect()
	return &Sys{conf: conf, t: t, mu: new(sync.Mutex)}
}

// command is a client command as Rabia's carry it (Command.Commands; roles/client's
// sendOneRequest): the operation type ("0" a write, "1" a read), the key (KeyLen bytes: Gen's keys
// have that length) and a write's value.
func command(in In) string {
	if in.Put {
		return "0" + in.K + in.V
	}
	return "1" + in.K
}

// Op is client c's operation, run on client machine c with its endpoint (newClient's Sys), one
// request as Rabia's closed-loop client sends it: a Command with the client's id, a fresh sequence
// number and one command ("0"+key+value for a put, "1"+key for a get) on the endpoint's send
// channel; then the client waits for the reply with that sequence number on the endpoint's
// receive channel (replies with another sequence number, to an earlier operation that gave up,
// are skipped), for at most OpMs: no reply in time is an unknown outcome, and the client goes on
// with a fresh sequence number. The reply's command is the proxy's execution result: "0"+key+"ok"
// for a put, "1"+key+value for a get (an empty value: not found; Gen's values are never empty).
func Op(x *Sys, c uint64, in In) Out {
	x.mu.Lock()
	out := op1(x, c, in)
	x.mu.Unlock()
	return out
}

// SeqBudget bounds a client's sequence numbers (Rabia's proxy numbers a client's requests by them,
// in increasing order): an operation past it answers unknown without sending anything. The
// orchestrator makes K operations per client; remote.ServeClient's contract allows any number.
const SeqBudget uint32 = 1 << 29

// op1 is Op's body, run with x.mu held.
func op1(x *Sys, c uint64, in In) Out {
	if x.next >= SeqBudget {
		return Out{Unknown: true}
	}
	seq := x.next
	x.next++
	x.t.SendChan <- message.Command{CliId: uint32(c), CliSeq: seq, Commands: []string{command(in)}}
	timeout := time.After(time.Duration(OpMs) * time.Millisecond)
	for {
		select {
		case rep := <-x.t.RecvChan:
			if rep.CliSeq != seq {
				continue
			}
			if len(rep.Commands) != 1 {
				panic("rabianet: a reply without one result")
			}
			r := rep.Commands[0]
			if in.Put {
				return Out{Put: true}
			}
			if uint64(len(r)) < 1+KeyLen {
				panic("rabianet: a get's result shorter than its key")
			}
			v := r[1+KeyLen:]
			return Out{Found: v != "", V: v}
		case <-timeout:
			return Out{Unknown: true}
		}
	}
}

// Client is client machine c's program (c < NC): its Rabia client endpoint, made once before
// serving (remote.ServeClient's newClient may be called any number of times as far as its
// contract says, and it waits for the configuration at a listener of its own), served at its
// address in ClientAddrs. It never returns.
func Client(c uint64) {
	sys := newClient(c)
	mk := func(id int) any {
		return sys
	}
	op := func(s any, in any) any {
		return Op(s.(*Sys), c, in.(In))
	}
	remote.ServeClient(int(c), ClientAddrs()[c], mk, op, Codec(), attempt())
}

// serveAt runs Rabia server id-1 of the configuration conf with its proxy at proxyAddr and the
// servers' network addresses ps: ServerInit with its proxy address and its network address,
// Prologue (the signal listener, the network layer's connections to every server, itself
// included, the proxy's accept routine, the terminal logger), then ServerMain (the proxy, network
// and consensus routines; it returns only when the server is told to exit, which nothing in the
// deployment does).
func serveAt(id uint64, proxyAddr string, ps []string, conf Conf) {
	configure(ps, conf)
	svr := server.ServerInit(uint32(id-1), proxyAddr, ps[id-1])
	svr.Prologue()
	svr.ServerMain()
}

// Server is server machine id's program (1 <= id <= MaxServers): it waits for the configuration
// and, if id is one of its N servers, runs Rabia server id-1 (main.go's RunServer without the
// benchmark controller); else it only waits. It never returns.
func Server(id uint64) {
	conf := waitConf(ServerConfAddrs()[id-1])
	if id <= conf.N {
		serveAt(id, ProxyAddrs()[id-1], NetAddrs()[:conf.N], conf)
	}
	for {
		time.Sleep(10 * time.Second)
	}
}
