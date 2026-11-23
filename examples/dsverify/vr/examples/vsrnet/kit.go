// Package vsrnet is the vr kit (dsverify-lab's vsr-bump-1, notes/dsv-vr.md) as an instance of
// examples/lib/remote: go-vsr's Viewstamped Replication over TCP (Go's net package), a key-value
// map replicated by 3 or 5 replicas, whose clients each run on a machine of their own, checked by
// porcupine on an orchestrator machine. Twelve machines, each a command of cmd/:
//
//   - the orchestrator (Orch, machine 0): it chooses the configuration at random and sends it to
//     every client machine and to the server machines that run a replica (Configure), then
//     remote.Check of NC clients' puts and gets, made at the clients' own machines, against the
//     key-value map with pending puts (Model);
//   - client machine c (Client, machine 1+c): it waits for the configuration, makes its go-vsr
//     client (id c+1, over a network.TCP of its own), then remote.ServeClient whose operation is
//     one request through that client (Op);
//   - server machine id (Server, machine NC+id, 1 <= id <= MaxReplicas): it waits for the
//     configuration and, if id <= N, runs replica id-1 serving the key-value store vsrkv; a server
//     machine that is not one of the N replicas only waits.
//
// An operation whose call fails, or that gets no reply in time, has an unknown outcome
// (Out{Unknown: true}): a put may have taken effect, may take effect later, or never.
//
// (dsverify-lab's kit ran the orchestrator with the lab's driver, recorder and kv checker
// (harness/remote's RunRemote and check.KV); here they are remote's, lintest's and porcupine's,
// with the kit's own model. Addresses are loopback, a port per machine and role.)
package vsrnet

import (
	"io"
	"log/slog"
	"net"
	"time"

	"github.com/anishathalye/porcupine"
	"github.com/goose-lang/primitive"
	"github.com/mit-pdos/etcd-grove/examples/lib/remote"
	"github.com/tangledbytes/go-vsr/examples/vsrkv"
	// vsrwire's init sets events' frame decoder (decoding a frame into vsrwire.Frame); the lab's
	// kit linked it through its generated JSON codec (json_gen.go, which encodes vsrwire.Frame),
	// which this port does not have yet (notes/dsv-vr.md, finding 2).
	_ "github.com/tangledbytes/go-vsr/examples/vsrwire"
	"github.com/tangledbytes/go-vsr/pkg/client"
	"github.com/tangledbytes/go-vsr/pkg/network"
	"github.com/tangledbytes/go-vsr/pkg/replica"
	vsrtime "github.com/tangledbytes/go-vsr/pkg/time"
)

// The configuration: NC clients, Ops operations each, at most MaxReplicas replicas, NKeys keys;
// a client's poll period PollMs and number of polls OpPolls per operation, a replica's event
// loop's pause LoopUs, a retry's wait RetryMs, a client's wait StartMs before its first
// operation (the replicas' start-up), plus StaggerMs per client.
const (
	NC          uint64 = 6
	Ops         uint64 = 8
	MaxReplicas uint64 = 5
	NKeys       uint64 = 2
	PollMs      uint64 = 5
	OpPolls     uint64 = 1600
	LoopUs      uint64 = 200
	RetryMs     uint64 = 100
	StartMs     uint64 = 3000
	StaggerMs   uint64 = 300
)

// AttemptMs bounds one call between the orchestrator and a client machine: a first operation's
// start and its polls, with time to spare.
const AttemptMs uint64 = 15000

// Addrs is every machine's go-vsr address, by machine: 0 the orchestrator (unused), 1..NC the
// client machines (client c on machine 1+c), then the server machines.
func Addrs() []string {
	return []string{
		"127.0.0.1:7500",
		"127.0.0.1:7501",
		"127.0.0.1:7502",
		"127.0.0.1:7503",
		"127.0.0.1:7504",
		"127.0.0.1:7505",
		"127.0.0.1:7506",
		"127.0.0.1:7507",
		"127.0.0.1:7508",
		"127.0.0.1:7509",
		"127.0.0.1:7510",
		"127.0.0.1:7511",
	}
}

// CfgAddrs is every machine's configuration address, by machine (the orchestrator's unused):
// where it waits for the configuration the orchestrator chose.
func CfgAddrs() []string {
	return []string{
		"127.0.0.1:7520",
		"127.0.0.1:7521",
		"127.0.0.1:7522",
		"127.0.0.1:7523",
		"127.0.0.1:7524",
		"127.0.0.1:7525",
		"127.0.0.1:7526",
		"127.0.0.1:7527",
		"127.0.0.1:7528",
		"127.0.0.1:7529",
		"127.0.0.1:7530",
		"127.0.0.1:7531",
	}
}

// ClientAddrs is the client machines' addresses for the orchestrator's calls (remote.Serve),
// client c's at index c.
func ClientAddrs() []string {
	return []string{
		"127.0.0.1:7541",
		"127.0.0.1:7542",
		"127.0.0.1:7543",
		"127.0.0.1:7544",
		"127.0.0.1:7545",
		"127.0.0.1:7546",
	}
}

// confAck is a machine's answer to a configuration it accepted.
const confAck = 0x6b

// Conf is a configuration of the deployment: the number of replicas and the timeouts of go-vsr's
// replica.Config and client.Config, as positions in heartbeatMs's and requestMs's lists (a backup
// starts a view change after twice the heartbeat timeout without a message from the primary; the
// primary sends a Commit after a heartbeat timeout; a client broadcasts its pending request to
// every replica after its request timeout).
type Conf struct {
	N         uint64 // replicas: 3 or 5 (f = 1 or 2), on server machines 1..N, replica ids 0..N-1
	Heartbeat uint64 // replica.Config's HeartbeatTimeout: heartbeatMs(Heartbeat) ms
	Request   uint64 // client.Config's RequestTimeout: requestMs(Request) ms
}

// NHeartbeats and NRequests are the number of heartbeat and request timeouts choose picks from.
const NHeartbeats = 8
const NRequests = 7

// heartbeatMs is the i-th heartbeat timeout, in ms (i < NHeartbeats): 1, 2, 3, 5, 10, 20, 100, 500.
// Time is not modeled, so in the theorem the values do not matter; in a test, timeouts of 10 ms
// or less make backups start view changes without any fault, and the longer ones run without them.
func heartbeatMs(i uint64) uint64 {
	return []uint64{1, 2, 3, 5, 10, 20, 100, 500}[i]
}

// requestMs is the i-th request timeout, in ms (i < NRequests): 10, 20, 50, 100, 200, 500, 1000.
func requestMs(i uint64) uint64 {
	return []uint64{10, 20, 50, 100, 200, 500, 1000}[i]
}

// choose picks a configuration at random (in the theorem, any choice).
func choose() Conf {
	n := uint64(3)
	if primitive.RandomUint64()%2 == 1 {
		n = 5
	}
	return Conf{N: n, Heartbeat: primitive.RandomUint64() % NHeartbeats,
		Request: primitive.RandomUint64() % NRequests}
}

// encode is c on the wire: three bytes, N, Heartbeat and Request.
func (c Conf) encode() []byte {
	return []byte{byte(c.N), byte(c.Heartbeat), byte(c.Request)}
}

// decode is the configuration b encodes, if b is one choose can pick.
func decode(b []byte) (Conf, bool) {
	c := Conf{N: uint64(b[0]), Heartbeat: uint64(b[1]), Request: uint64(b[2])}
	return c, (c.N == 3 || c.N == 5) && c.Heartbeat < NHeartbeats && c.Request < NRequests
}

// sendConf sends the configuration b to the machine at addr and waits for its acknowledgment;
// true if acknowledged.
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

// Configure sends the configuration conf to every client machine and to server machines
// 1..conf.N, machine n at its configuration address cfgs[n], each until it acknowledges it.
func Configure(cfgs []string, conf Conf) {
	for n := uint64(1); n <= NC+conf.N; n++ {
		for !sendConf(cfgs[n], conf.encode()) {
			time.Sleep(time.Duration(RetryMs) * time.Millisecond)
		}
	}
}

// awaitConf listens on addr (retrying a failed Listen) and answers every configuration it reads
// with an acknowledgment (the orchestrator sends again until it has one); the first is sent on
// ch. A connection that fails, or whose bytes are not a configuration, is closed without an
// answer.
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
		var b [3]byte
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

// waitConf is the configuration machine n receives at its configuration address cfgs[n].
func waitConf(cfgs []string, n uint64) Conf {
	ch := make(chan Conf, 1)
	go awaitConf(cfgs[n], ch)
	return <-ch
}

// replicas is the replicas' addresses in the configuration conf: server machines 1..conf.N.
func replicas(addrs []string, conf Conf) []string {
	return addrs[NC+1 : NC+1+conf.N]
}

// logger is the logger every go-vsr client and replica gets: it writes nothing (go-vsr's
// cmd/example passes none, and a nil *slog.Logger panics at the first log call).
func logger() *slog.Logger {
	return slog.New(slog.DiscardHandler)
}

// Sys is a client machine's view of the deployment: its go-vsr client over a network.TCP of its
// own (it dials the replicas; it never listens), the client's index, whether it has made an
// operation yet, and whether one of its operations gave up while its request was still pending
// (go-vsr's client then refuses every later request).
type Sys struct {
	net     *network.TCP
	c       *client.Client
	id      uint64
	started bool
	gaveUp  bool
}

// mkClient is client c's go-vsr client, id c+1, over a network.TCP at its machine's address
// addrs[1+c], with the configuration conf's replicas.
func mkClient(addrs []string, conf Conf, c uint64) *Sys {
	RegisterJSON()
	tcp := network.NewTCP(addrs[1+c])
	vc, err := client.New(client.Config{
		ID:             c + 1,
		Members:        replicas(addrs, conf),
		Network:        tcp,
		Time:           vsrtime.NewReal(),
		RequestTimeout: requestMs(conf.Request) * vsrtime.MILLISECOND,
		Logger:         logger(),
	})
	if err != nil {
		panic("vsrnet: client.New")
	}
	return &Sys{net: tcp, c: vc, id: c}
}

// In is an operation's input: a put of V at K, or a get of K.
type In struct {
	Put bool
	K   string
	V   string
}

// Out is an operation's output: for a get, whether K has a value and the value; Done for a put
// (so that a put's output and a get's "not found" differ: remote's codec must tell outputs apart);
// or Unknown (the operation's outcome is unknown).
type Out struct {
	Unknown bool
	Done    bool
	Found   bool
	V       string
}

// Op is client machine c's operation through its go-vsr client: Request("SET k v") for a put,
// Request("GET k") for a get, then the client's loop (the replies its network.TCP received
// submitted to it, Run, CheckResult) until a reply, or until OpPolls rounds (PollMs apart) have
// passed: an unknown outcome, after which the client has a request pending and every later
// operation of c is unknown too. A false Request means the request is pending but its send
// failed (go-vsr's Request): the loop goes on (go-vsr's client retries by broadcasting after its
// timeout). A get's reply is the key's value (empty: not found; Gen's values are never empty).
// The first operation waits StartMs + c*StaggerMs before it starts.
func Op(s any, in any) any {
	x := s.(*Sys)
	if !x.started {
		x.started = true
		time.Sleep(time.Duration(StartMs+x.id*StaggerMs) * time.Millisecond)
	}
	if x.gaveUp {
		return Out{Unknown: true}
	}
	kv := in.(In)
	op := "GET " + kv.K
	if kv.Put {
		op = "SET " + kv.K + " " + kv.V
	}
	x.c.Request(op)
	for i := uint64(0); i < OpPolls; i++ {
		for {
			ev, ok := x.net.Recv()
			if !ok {
				break
			}
			x.c.Submit(ev)
		}
		x.c.Run()
		rep, ok := x.c.CheckResult()
		if ok {
			if kv.Put {
				return Out{Done: true}
			}
			if rep.Result == "" {
				return Out{}
			}
			return Out{Found: true, V: rep.Result}
		}
		time.Sleep(time.Duration(PollMs) * time.Millisecond)
	}
	x.gaveUp = true
	return Out{Unknown: true}
}

// Pair is a key and a value.
type Pair struct {
	K string
	V string
}

// State is the model's state: the map's value of each key that has one (Cur, one pair per key)
// and the puts of unknown outcome (Pend; each may still take effect, once, or never). It stands
// for the map Cur with any of Pend's puts still to take effect: every other configuration that
// the history allows (some of Pend's puts having taken effect and been overwritten) allows no
// more later outcomes than this one.
type State struct {
	Cur  []Pair
	Pend []Pair
}

// lookup is k's value in p, if it has one. (The helpers read each element into a local first:
// a whole element's load, which the proofs take from the read-only slice.)
func lookup(p []Pair, k string) (string, bool) {
	for i := 0; i < len(p); i++ {
		e := p[i]
		if e.K == k {
			return e.V, true
		}
	}
	return "", false
}

// set is p with k's value v, in a new slice (states are never written).
func set(p []Pair, k string, v string) []Pair {
	q := make([]Pair, 0, len(p)+1)
	found := false
	for i := 0; i < len(p); i++ {
		e := p[i]
		if e.K == k {
			q = append(q, Pair{K: k, V: v})
			found = true
		} else {
			q = append(q, e)
		}
	}
	if !found {
		q = append(q, Pair{K: k, V: v})
	}
	return q
}

// has reports whether x is in p.
func has(p []Pair, x Pair) bool {
	for i := 0; i < len(p); i++ {
		e := p[i]
		if e.K == x.K && e.V == x.V {
			return true
		}
	}
	return false
}

// erase is p without its first x, in a new slice.
func erase(p []Pair, x Pair) []Pair {
	q := make([]Pair, 0, len(p))
	found := false
	for i := 0; i < len(p); i++ {
		e := p[i]
		if !found && e.K == x.K && e.V == x.V {
			found = true
		} else {
			q = append(q, e)
		}
	}
	return q
}

// push is p with x added, in a new slice.
func push(p []Pair, x Pair) []Pair {
	q := make([]Pair, len(p)+1)
	copy(q, p)
	q[len(p)] = x
	return q
}

// step is the model's step: a put of unknown outcome is pending, a get of unknown outcome
// changes nothing; an answered put (Done) takes effect; an answered get of K finds K's value, or V if a
// pending put of V at K takes effect first (it leaves Pend), or nothing if K has no value.
func step(s State, in In, o Out) (bool, State) {
	if o.Unknown {
		if in.Put {
			return true, State{Cur: s.Cur, Pend: push(s.Pend, Pair{K: in.K, V: in.V})}
		}
		return true, s
	}
	if in.Put {
		if !o.Done {
			return false, s
		}
		return true, State{Cur: set(s.Cur, in.K, in.V), Pend: s.Pend}
	}
	if o.Done {
		return false, s
	}
	v, ok := lookup(s.Cur, in.K)
	if !o.Found {
		return !ok, s
	}
	if ok && v == o.V {
		return true, s
	}
	x := Pair{K: in.K, V: o.V}
	if has(s.Pend, x) {
		return true, State{Cur: set(s.Cur, in.K, o.V), Pend: erase(s.Pend, x)}
	}
	return false, s
}

// equalPairs reports whether a and b are the same list.
func equalPairs(a []Pair, b []Pair) bool {
	if len(a) != len(b) {
		return false
	}
	for i := 0; i < len(a); i++ {
		x := a[i]
		y := b[i]
		if x.K != y.K || x.V != y.V {
			return false
		}
	}
	return true
}

// Model's Equal says two states are equal only when nothing is pending: a state with pending puts
// stands for a set of configurations that the history determines and the state does not (it
// stands for that set up to configurations that allow no more outcomes), while a state with nothing
// pending stands for exactly one configuration (notes/dsv-vr.md, "the model's Equal").
//
// Model is the key-value map with pending puts (linkv's pending-writes model of the map: puts are
// its writes), as a porcupine model. Inputs are Ins, outputs Outs.
func Model() porcupine.Model {
	return porcupine.Model{
		Init: func() any { return State{} },
		Step: func(state, input, output any) (bool, any) {
			ok, s := step(state.(State), input.(In), output.(Out))
			return ok, s
		},
		Equal: func(a, b any) bool {
			x := a.(State)
			y := b.(State)
			return len(x.Pend) == 0 && len(y.Pend) == 0 && equalPairs(x.Cur, y.Cur)
		},
	}
}

// Codec is the map's codec: an input as one byte (1: put), K's length, K and V; an output as one
// byte (1: unknown), one byte (1: found) and V.
func Codec() remote.Codec {
	return remote.Codec{
		EncIn: func(in any) []byte {
			x := in.(In)
			b := make([]byte, 2, 2+len(x.K)+len(x.V))
			if x.Put {
				b[0] = 1
			}
			b[1] = byte(len(x.K))
			b = append(b, []byte(x.K)...)
			return append(b, []byte(x.V)...)
		},
		DecIn: func(b []byte) (any, bool) {
			if len(b) < 2 || b[0] > 1 || 2+uint64(b[1]) > uint64(len(b)) {
				return nil, false
			}
			k := 2 + uint64(b[1])
			return In{Put: b[0] == 1, K: string(b[2:k]), V: string(b[k:])}, true
		},
		EncOut: func(out any) []byte {
			o := out.(Out)
			b := make([]byte, 3, 3+len(o.V))
			if o.Unknown {
				b[0] = 1
			}
			if o.Done {
				b[1] = 1
			}
			if o.Found {
				b[2] = 1
			}
			return append(b, []byte(o.V)...)
		},
		DecOut: func(b []byte) (any, bool) {
			if len(b) < 3 || b[0] > 1 || b[1] > 1 || b[2] > 1 {
				return nil, false
			}
			return Out{Unknown: b[0] == 1, Done: b[1] == 1, Found: b[2] == 1, V: string(b[3:])}, true
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

// digits is n in decimal.
func digits(n uint64) string {
	if n < 10 {
		return digit(n)
	}
	return digits(n/10) + digit(n)
}

// Gen is client c's next input, at random (in the theorem, any choice): a put or a get of key
// "k<i>" (i < NKeys); a put's value is "v<c><r>" (c's one digit, then r < 1000 in decimal), never
// empty and without spaces (c below 10).
func Gen(c int) any {
	r := primitive.RandomUint64()
	k := "k" + digit((r/2)%NKeys)
	if r%2 == 0 {
		return In{Put: true, K: k, V: "v" + digit(uint64(c)) + digits((r/(2*NKeys))%1000)}
	}
	return In{Put: false, K: k, V: ""}
}

// attempt is AttemptMs as a duration.
func attempt() time.Duration {
	return time.Duration(AttemptMs) * time.Millisecond
}

// Orch is the orchestrator's program: it chooses and sends the configuration, then panics unless
// porcupine accepts the history of the clients' operations.
func Orch() {
	Configure(CfgAddrs(), choose())
	remote.Check(Model(), ClientAddrs(), Codec(), Gen, int(Ops), attempt())
}

// Client is client machine c's program (c < NC): it waits for the configuration, makes its go-vsr
// client once, before serving (as paxos's kit: remote.ServeClient's newClient may be called any
// number of times as far as its contract says, and a second go-vsr client of id c+1 would reuse
// its request ids), and serves the orchestrator's calls at its address in ClientAddrs with Op.
func Client(c uint64) {
	sys := mkClient(Addrs(), waitConf(CfgAddrs(), 1+c), c)
	newClient := func(id int) any {
		return sys
	}
	remote.ServeClient(int(c), ClientAddrs()[c], newClient, Op, Codec(), attempt())
}

// Server is server machine id's program (1 <= id <= MaxReplicas, machine NC+id): it waits for the
// configuration, then runs replica id-1 if id <= N, else only waits. It never returns.
func Server(id uint64) {
	conf := waitConf(CfgAddrs(), NC+id)
	if id <= conf.N {
		runReplica(id, Addrs(), conf)
	}
	for {
		time.Sleep(10 * time.Second)
	}
}

// runReplica runs replica id-1 of the configuration conf at server machine id's address
// addrs[NC+id], with the configuration's replicas, serving the key-value store vsrkv (go-vsr's
// cmd/example server's event loop: the network's events submitted to the replica, the replica
// run, and a pause when nothing arrived).
func runReplica(id uint64, addrs []string, conf Conf) {
	RegisterJSON()
	tcp := network.NewTCP(addrs[NC+id])
	store := vsrkv.New()
	r, err := replica.New(replica.Config{
		HeartbeatTimeout: heartbeatMs(conf.Heartbeat) * vsrtime.MILLISECOND,
		SrvHandler:       store.Handle,
		Network:          tcp,
		Time:             vsrtime.NewReal(),
		ID:               id - 1,
		Members:          replicas(addrs, conf),
		Logger:           logger(),
	})
	if err != nil {
		return
	}
	go tcp.Run()
	for {
		ev, ok := tcp.Recv()
		if ok {
			r.Submit(ev)
		}
		r.Run()
		if !ok {
			time.Sleep(time.Duration(LoopUs) * time.Microsecond)
		}
	}
}
