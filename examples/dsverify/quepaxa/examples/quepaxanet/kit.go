// Package quepaxanet is the QuePaxa kit (dsverify-lab's quepaxa-bump-1, notes/dsv-quepaxa.md) as an
// instance of examples/lib/remote: QuePaxa's replicated key-value store over TCP (Go's net package,
// and gRPC between the replicas' proposers and recorders), whose clients each run on a machine of
// their own, checked by porcupine on an orchestrator machine. Twelve machines, each a command of
// cmd/:
//
//   - the orchestrator (Orch): it chooses the deployment's configuration at random and sends it to
//     every client machine and to the server machines that run replicas (New), then remote.Check of
//     NC clients' K operations each, made at the clients' own machines, against the key-value map
//     with pending puts (Model, model.go);
//   - client machine c (Client, c < NC): its QuePaxa client (NewClient: it waits for the
//     configuration, listens for the replicas' connections back and connects to every replica's
//     proxy), then remote.ServeClient whose operation is Op over that client (at most K requests:
//     later operations are unknown);
//   - server machine id (Server, 1 <= id <= MaxReplicas): it waits for the configuration; if it is
//     one of the configuration's replicas it runs QuePaxa replica id, as replica/main.go runs it.
//
// The configuration (Conf): 3 or 5 replicas (on server machines 1..N; with 3, server machines 4
// and 5 never get one and only wait), leader mode 2 (the multi-armed bandit), server mode 0 or 1,
// a pipeline of 1 to 5 slots, epochs of 1 to 5 slots, and a leader timeout of 5 to 40 ms.
//
// An operation that gets no answer in time has an unknown outcome (Out{Unknown: true}): a put may
// have taken effect, may take effect later, or never (the model's pending put); a get changes
// nothing.
//
// (dsverify-lab's kit ran the orchestrator with its own remote driver, recorder and check.KV over
// its models.KvIn/KvOut, with unknown outcomes as porcupine's pending operations, and the nodes at
// 10.77.0.x with the same ports on every host; here they are remote's, lintest's and porcupine's,
// the model is the kit's own (model.go), and every node's addresses are distinct ports of
// 127.0.0.1 (address lists in place of the lab's ports(addrs, port)).)
package quepaxanet

import (
	"bufio"
	"encoding/binary"
	"io"
	"log"
	"math/rand"
	"net"
	"strings"
	"sync"
	"time"

	"github.com/mit-pdos/etcd-grove/examples/lib/remote"
	"raxos/configuration"
	"raxos/proto/client"
	raxos "raxos/replica/src"
)

// The configuration (the lab's kit.toml): NC clients, K operations each, at most MaxReplicas
// replicas, NKeys keys of KeyLen bytes (values of ValLen bytes in QuePaxa's flags), the first
// client's QuePaxa name ClientName, QuePaxa's constant flags (BatchSize, BatchTimeUs, LeaderMode,
// TimeEpochMs), an operation's wait for its answer OpMs, Listen's and Dial's retry RetryMs, the
// orchestrator's wait for the deployment's start StartMs, and the bound on a client's random wait
// before its first operation, NC*StaggerMs.
const (
	NC          uint64 = 6
	K           uint64 = 20
	MaxReplicas uint64 = 5
	NKeys       uint64 = 2
	KeyLen      uint64 = 8
	ValLen      uint64 = 8
	ClientName  uint64 = 21
	BatchSize   uint64 = 50
	BatchTimeUs uint64 = 0
	LeaderMode  uint64 = 2
	TimeEpochMs uint64 = 500
	OpMs        uint64 = 2000
	RetryMs     uint64 = 100
	StartMs     uint64 = 3000
	StaggerMs   uint64 = 1000
)

// AttemptMs bounds one call between the orchestrator and a client machine: a client's stagger and
// an operation's wait, with time to spare.
const AttemptMs uint64 = OpMs + NC*StaggerMs + 2000

// Addrs is every node's first address, by node id: node 0 the orchestrator (unused), nodes 1..NC
// the client machines (client c on node 1+c: its QuePaxa client's listener, where the replicas
// connect back), then server machines 1..MaxReplicas (server machine k on node NC+k: its replica's
// proxy, where clients connect).
func Addrs() []string {
	return []string{
		"127.0.0.1:7600",
		"127.0.0.1:7601",
		"127.0.0.1:7602",
		"127.0.0.1:7603",
		"127.0.0.1:7604",
		"127.0.0.1:7605",
		"127.0.0.1:7606",
		"127.0.0.1:7607",
		"127.0.0.1:7608",
		"127.0.0.1:7609",
		"127.0.0.1:7610",
		"127.0.0.1:7611",
	}
}

// RecAddrs is every node's recorder (gRPC) address, by node id (only the server machines'
// are used).
func RecAddrs() []string {
	return []string{
		"127.0.0.1:7620",
		"127.0.0.1:7621",
		"127.0.0.1:7622",
		"127.0.0.1:7623",
		"127.0.0.1:7624",
		"127.0.0.1:7625",
		"127.0.0.1:7626",
		"127.0.0.1:7627",
		"127.0.0.1:7628",
		"127.0.0.1:7629",
		"127.0.0.1:7630",
		"127.0.0.1:7631",
	}
}

// CfgAddrs is every node's configuration address, by node id, where a client or server machine
// waits for the configuration the orchestrator chose (the orchestrator's is unused).
func CfgAddrs() []string {
	return []string{
		"127.0.0.1:7640",
		"127.0.0.1:7641",
		"127.0.0.1:7642",
		"127.0.0.1:7643",
		"127.0.0.1:7644",
		"127.0.0.1:7645",
		"127.0.0.1:7646",
		"127.0.0.1:7647",
		"127.0.0.1:7648",
		"127.0.0.1:7649",
		"127.0.0.1:7650",
		"127.0.0.1:7651",
	}
}

// ClientAddrs is the client machines' addresses for the orchestrator's calls (remote.Serve),
// client c's at index c.
func ClientAddrs() []string {
	return []string{
		"127.0.0.1:7661",
		"127.0.0.1:7662",
		"127.0.0.1:7663",
		"127.0.0.1:7664",
		"127.0.0.1:7665",
		"127.0.0.1:7666",
	}
}

// confAck is a node's answer to a configuration it accepted.
const confAck = 0x6b

// confLen is the length of a configuration on the wire (encode).
const confLen = 5

// Conf is a configuration of the deployment: the number of replicas (3 or 5: server machines
// 1..N) and the values of replica/main.go's flags that vary (the others are the constants above:
// leader mode 2, batch size, batch time, benchmark mode 0, key length).
type Conf struct {
	N          uint64 // replicas: 3 or 5
	ServerMode uint64 // main.go's -serverMode: 0 or 1
	Pipeline   uint64 // main.go's -pipelineLength: 1..5
	Epoch      uint64 // main.go's -epochSize: 1..5
	TimeoutUs  uint64 // main.go's -leaderTimeout: 5000, 10000, ..., 40000
}

// choose picks a configuration at random (math/rand: in the theorem, any choice).
func choose() Conf {
	n := uint64(3)
	if rand.Intn(2) == 1 {
		n = 5
	}
	return Conf{N: n, ServerMode: uint64(rand.Intn(2)), Pipeline: 1 + uint64(rand.Intn(5)),
		Epoch: 1 + uint64(rand.Intn(5)), TimeoutUs: 5000 + 5000*uint64(rand.Intn(8))}
}

// encode is c on the wire: five bytes, N, ServerMode, Pipeline, Epoch, TimeoutUs/5000.
func (c Conf) encode() []byte {
	return []byte{byte(c.N), byte(c.ServerMode), byte(c.Pipeline), byte(c.Epoch), byte(c.TimeoutUs / 5000)}
}

// decode is the configuration b (confLen bytes) encodes, if b is one choose can pick.
func decode(b []byte) (Conf, bool) {
	c := Conf{N: uint64(b[0]), ServerMode: uint64(b[1]), Pipeline: uint64(b[2]), Epoch: uint64(b[3]),
		TimeoutUs: 5000 * uint64(b[4])}
	ok := (c.N == 3 || c.N == 5) && c.ServerMode <= 1 && 1 <= c.Pipeline && c.Pipeline <= 5 &&
		1 <= c.Epoch && c.Epoch <= 5 && 5000 <= c.TimeoutUs && c.TimeoutUs <= 40000
	return c, ok
}

// String is c for the log: "replicas N, server mode S, pipeline P, epochs of E, leader timeout T us".
func (c Conf) String() string {
	return "replicas " + digits(c.N) + ", server mode " + digits(c.ServerMode) + ", pipeline " +
		digits(c.Pipeline) + ", epochs of " + digits(c.Epoch) + ", leader timeout " + digits(c.TimeoutUs) + " us"
}

// LogPath is QuePaxa's logFilePath, where its status operations write logs (no operation of this
// kit's reaches them).
const LogPath = "/tmp/quepaxa-net/"

// NotFound is a get's result for a key never put (QuePaxa's resident store answers "1"+key+"nil").
const NotFound = "nil"

// clientBatchRpc is QuePaxa's code for a ClientBatch on a proxy connection (the proxy's and the
// benchmark client's clientBatchRpc).
const clientBatchRpc = 1

// New is the orchestrator's setup of the deployment: it chooses the configuration at random and
// sends it to every node that needs it, at the nodes' configuration addresses cfgs.
func New(cfgs []string) {
	send(cfgs, choose())
}

// send sends the configuration conf to every client machine and to server machines 1..conf.N
// (nodes NC+1..NC+conf.N), node n at its configuration address cfgs[n], each until it
// acknowledges it.
func send(cfgs []string, conf Conf) {
	log.Println("quepaxanet: configuration: " + conf.String())
	for n := uint64(1); n <= NC+conf.N; n++ {
		for !sendConf(cfgs[n], conf.encode()) {
			time.Sleep(time.Duration(RetryMs) * time.Millisecond)
		}
	}
}

// sendConf sends the configuration b to the node at addr and waits for its acknowledgment; true
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

// replica is a client machine's connection to one replica's proxy: a TCP connection that starts
// with the client's handshake (its name, as QuePaxa's client sends it), then carries ClientBatch
// messages (a code byte and the batch's length-prefixed protobuf encoding, QuePaxa's
// clientwrapper.go). The proxy answers over a connection of its own, which it dials back to the
// client machine's listener when it accepts this one.
type replica struct {
	mu   sync.Mutex
	name uint64 // the client's QuePaxa name, for the handshake
	addr string
	c    net.Conn // nil: not connected
	w    *bufio.Writer
}

// Sys is a client machine's view of the deployment: client c as one QuePaxa client (name
// ClientName+c) connected to every replica's proxy, matching answers to its requests by batch id,
// and the sequence number of its next request (both under mu).
type Sys struct {
	conf     Conf
	c        uint64
	name     uint64 // ClientName + c
	checks   bool
	mu       sync.Mutex
	waiting  map[string]chan *client.ClientBatch // batch id -> the waiting operation's channel
	answered map[string]bool                     // checks only: "replica/batch id" answered
	replicas []*replica
	next     uint64
}

// NewClient is client c's machine's side of the deployment: it waits for the configuration and
// makes client c's QuePaxa client, without the stress test's checks.
func NewClient(c uint64) *Sys {
	return newClient(Addrs(), CfgAddrs(), c, false)
}

// newClient is NewClient in the deployment at addrs, with the nodes' configuration addresses
// cfgs (each indexed by node; kit_test.go's on free loopback ports): it waits for the
// configuration on cfgs[1+c], registers the protobuf model's codec, listens on its node's address
// addrs[1+c] for the replicas' connections back to the client (QuePaxa's client listens on its
// configured address; each proxy dials it when the client connects), and connects to every
// replica's proxy (server machines 1..N, nodes NC+1..NC+N; retrying until each accepts, as
// QuePaxa's client connects to every replica before it sends). With checks (the stress test
// only), a replica that answers a request twice panics (it executed the request twice).
func newClient(addrs []string, cfgs []string, c uint64, checks bool) *Sys {
	ch := make(chan Conf, 1)
	go awaitConf(cfgs[1+c], ch)
	conf := <-ch
	registerProto()
	s := &Sys{conf: conf, c: c, name: ClientName + c, checks: checks,
		waiting: make(map[string]chan *client.ClientBatch), answered: make(map[string]bool)}
	for i := uint64(1); i <= conf.N; i++ {
		s.replicas = append(s.replicas, &replica{name: s.name, addr: addrs[NC+i]})
	}
	// Listen may fail (the address may be in use for a while): retry, as the replicas must
	l, err := net.Listen("tcp", addrs[1+c])
	for err != nil {
		time.Sleep(time.Duration(RetryMs) * time.Millisecond)
		l, err = net.Listen("tcp", addrs[1+c])
	}
	go s.accept(l)
	for _, r := range s.replicas {
		for !r.tryConnect() {
			time.Sleep(time.Duration(RetryMs) * time.Millisecond)
		}
	}
	return s
}

// tryConnect connects to the replica's proxy if not connected; true if connected.
func (r *replica) tryConnect() bool {
	r.mu.Lock()
	ok := r.c != nil || r.connect()
	r.mu.Unlock()
	return ok
}

// connect dials the replica's proxy and sends the handshake (the client's name in the first two
// of four bytes, little-endian, as QuePaxa's client sends it); true if connected. r.mu is held.
func (r *replica) connect() bool {
	c, err := net.Dial("tcp", r.addr)
	if err != nil {
		return false
	}
	var hs [4]byte
	binary.LittleEndian.PutUint16(hs[:], uint16(r.name))
	if _, err := c.Write(hs[:]); err != nil {
		c.Close()
		return false
	}
	r.c = c
	r.w = bufio.NewWriter(c)
	return true
}

// drop closes the connection (the next send reconnects). r.mu is held and r.c is not nil.
func (r *replica) drop() {
	r.c.Close()
	r.c = nil
	r.w = nil
}

// send writes batch b to the replica's proxy (connecting first if not connected); on an error the
// connection is dropped and b is not sent to this replica.
func (r *replica) send(b *client.ClientBatch) {
	r.mu.Lock()
	if r.c != nil || r.connect() {
		if r.w.WriteByte(clientBatchRpc) != nil || b.Marshal(r.w) != nil || r.w.Flush() != nil {
			r.drop()
		}
	}
	r.mu.Unlock()
}

// reset drops the connection to the replica's proxy, whose connection back to the client has
// ended: the next send reconnects, and the proxy, accepting, dials back again.
func (r *replica) reset() {
	r.mu.Lock()
	if r.c != nil {
		r.drop()
	}
	r.mu.Unlock()
}

// accept takes the replicas' connections back to the client.
func (s *Sys) accept(l net.Listener) {
	for {
		c, err := l.Accept()
		if err == nil {
			go s.receive(c)
		}
	}
}

// receive reads one replica's connection back to the client: the proxy's handshake (its name),
// then ClientBatch messages, the answers to requests, each delivered to the operation waiting for
// its batch id. When the connection ends, the client's connection to that replica is reset.
func (s *Sys) receive(c net.Conn) {
	rd := bufio.NewReader(c)
	var hs [4]byte
	if _, err := io.ReadFull(rd, hs[:]); err != nil {
		c.Close()
		return
	}
	from := uint64(binary.LittleEndian.Uint16(hs[:]))
	for {
		code, err := rd.ReadByte()
		if err != nil || code != clientBatchRpc {
			break
		}
		b := &client.ClientBatch{}
		if b.Unmarshal(rd) != nil {
			break
		}
		s.deliver(from, b)
	}
	c.Close()
	if 1 <= from && from <= uint64(len(s.replicas)) {
		s.replicas[from-1].reset()
	}
}

// deliver gives replica from's answer b to the operation waiting for its batch id, if any (the
// first answer counts; a later one, from another replica, or one to an operation that gave up, is
// dropped).
func (s *Sys) deliver(from uint64, b *client.ClientBatch) {
	s.mu.Lock()
	if s.checks {
		k := digits(from) + "/" + b.Id
		if s.answered[k] {
			panic("quepaxanet: replica " + digits(from) + " answered request " + b.Id +
				" twice (it executed the request twice)")
		}
		s.answered[k] = true
	}
	ch, ok := s.waiting[b.Id]
	if ok {
		delete(s.waiting, b.Id)
		ch <- b
	}
	s.mu.Unlock()
}

// command is a request's command as QuePaxa's resident store reads it (replica/src/kvStore.go):
// the type ("0" a write, "1" a read), the key (KeyLen bytes: the inputs' keys have that length)
// and a write's value.
func command(in In) string {
	if in.Put {
		return "0" + in.K + in.V
	}
	return "1" + in.K
}

// Op is client c's operation, run on client machine c with its QuePaxa client (NewClient's Sys),
// one request as QuePaxa's benchmark client sends one: before the client's first request it waits
// a random 0 to NC*StaggerMs (time is not modeled: the theorem allows any delay); a ClientBatch from the client (its name the sender)
// with one command and a fresh batch id ("<name>.<seq>": distinct across the clients, whose names
// are) sent to every replica's proxy; then the first answer with that id, for at most OpMs: no
// answer in time is an unknown outcome (Out{Unknown: true}). An answer's command is the store's
// result: "0"+key+"ok" for a put, "1"+key+value for a get ("1"+key+"nil": not found; Gen's values
// are never "nil").
//
// The sequence number is taken under s.mu, and a client sends at most K requests: remote may run
// Op more than K times on a client machine (remote.Do retries a read, and a retried call may
// overlap the one it retries), and the replicas' slots are bounded by the workload's requests
// (NC clients, K each: notes/dsv-quepaxa.md). An operation past the budget has an unknown outcome
// without sending anything.
func Op(s *Sys, in In) Out {
	s.mu.Lock()
	seq := s.next
	if seq < K {
		s.next = seq + 1
	}
	s.mu.Unlock()
	if seq >= K {
		return Out{Unknown: true}
	}
	if seq == 0 {
		time.Sleep(time.Duration(rand.Intn(int(NC*StaggerMs)+1)) * time.Millisecond)
	}
	id := digits(s.name) + "." + digits(seq)
	ch := make(chan *client.ClientBatch, 1)
	s.mu.Lock()
	s.waiting[id] = ch
	s.mu.Unlock()
	b := &client.ClientBatch{Sender: int64(s.name), Id: id,
		Messages: []*client.ClientBatch_SingleMessage{{Message: command(in)}}}
	for _, r := range s.replicas {
		r.send(b)
	}
	select {
	case rep := <-ch:
		return result(s.checks, in, rep)
	case <-time.After(time.Duration(OpMs) * time.Millisecond):
		s.mu.Lock()
		delete(s.waiting, id)
		s.mu.Unlock()
		return Out{Unknown: true}
	}
}

// result is the operation's output from the answer rep. With checks (the stress test only), the
// answer must be to a command of the request's type and key.
func result(checks bool, in In, rep *client.ClientBatch) Out {
	if len(rep.Messages) != 1 {
		panic("quepaxanet: an answer without one result")
	}
	r := rep.Messages[0].Message
	if uint64(len(r)) < 1+KeyLen {
		panic("quepaxanet: a result shorter than its key")
	}
	if checks && r[:1+KeyLen] != command(in)[:1+KeyLen] {
		panic("quepaxanet: an answer to another command")
	}
	if in.Put {
		return Out{}
	}
	v := r[1+KeyLen:]
	if v == NotFound {
		return Out{}
	}
	return Out{Found: true, V: v}
}

// mix is a fixed hash of client c's round r (multiply-xorshift, wrapping uint64 arithmetic): Gen's
// key for the round is mix(c, r) mod NKeys, so the rounds spread over the keys without a fixed
// per-client pattern of the keys' order and without state.
func mix(c uint64, r uint64) uint64 {
	x := c*0x9E3779B97F4A7C15 + r*0xBF58476D1CE4E5B9 + 1
	x ^= x >> 31
	x *= 0x94D049BB133111EB
	x ^= x >> 29
	return x
}

// Gen is client c's j-th input: a put (j even) and then a get (j odd) of the same key, round j/2's
// key "key0000<mix(c, j/2) mod NKeys>" (KeyLen, 8 bytes; the get reads the key its own put wrote,
// and every key is written and read by several clients); put values "v<c><j>" (c's one digit,
// then j in decimal) are distinct, never empty and never "nil" (c below 10).
func Gen(c uint64, j uint64) In {
	k := "key0000" + digit(mix(c, j/2)%NKeys)
	if j%2 == 0 {
		return In{Put: true, K: k, V: "v" + digit(c) + digits(j)}
	}
	return In{Put: false, K: k, V: ""}
}

// Gens is remote's generator over Gen: client c's i-th call gives Gen(c, i). remote's generator
// may be called for any c >= 0, concurrently (its spec is lintest's genSpec), so the counters are
// taken under a lock, client c's at index c mod NC.
func Gens() func(int) any {
	var mu sync.Mutex
	next := make([]uint64, NC)
	return func(c int) any {
		mu.Lock()
		i := uint64(c) % NC
		j := next[i]
		next[i] = j + 1
		mu.Unlock()
		return Gen(uint64(c), j)
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

// config is QuePaxa's configuration (configuration.yml's) of n replicas of the deployment at addrs
// with the nodes' recorder addresses recs (both indexed by node): replica i (name "i") at server
// machine i's (node NC+i's) host with its proxy's and its recorder's ports, and NC clients, client
// c (name ClientName+c) at client machine c's (node 1+c's) address. Unlike
// configuration.NewInstanceConfig, no replica's or client's own IP is replaced by 0.0.0.0 (every
// node dials its peers' configured addresses, itself included; QuePaxa listens on 0.0.0.0 anyway).
func config(n uint64, addrs []string, recs []string) *configuration.InstanceConfig {
	cfg := &configuration.InstanceConfig{}
	for i := uint64(1); i <= n; i++ {
		p := strings.Split(addrs[NC+i], ":")
		q := strings.Split(recs[NC+i], ":")
		cfg.Peers = append(cfg.Peers, configuration.ReplicaInstance{Name: digits(i), IP: p[0],
			PROXYPORT: p[1], RECORDERPORT: q[1]})
	}
	for c := uint64(0); c < NC; c++ {
		p := strings.Split(addrs[1+c], ":")
		cfg.Clients = append(cfg.Clients, configuration.ClientInstance{Name: digits(ClientName + c), IP: p[0],
			CLIENTPORT: p[1]})
	}
	return cfg
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

// serve runs server machine id of the deployment at addrs (proxies), with the nodes' recorder
// addresses recs and configuration addresses cfgs (each indexed by node: Server's; kit_test.go's
// on free loopback ports): it waits for the configuration; a replica then runs with main.go's
// flags as the configuration's and the constants above (batch size, batch time, leader timeout,
// pipeline length, leader mode with its epoch size, server mode, benchmark mode 0 (the resident
// store), key length, no request propagation time, no simulated asynchrony, debugging off), and
// its proposers started as the benchmark client's bootstrap status request (ClientStatus
// operation 1) starts them: Server.StartProposers. A server machine that is not one of the
// replicas only waits. It never returns.
func serve(id uint64, addrs []string, recs []string, cfgs []string) {
	ch := make(chan Conf, 1)
	go awaitConf(cfgs[NC+id], ch)
	conf := <-ch
	if id <= conf.N {
		registerProto()
		s := raxos.New(config(conf.N, addrs, recs), int64(id), LogPath, int64(BatchSize),
			int64(conf.TimeoutUs), int64(conf.Pipeline), false, 0, int(LeaderMode), int(conf.ServerMode),
			int64(BatchTimeUs), int(conf.Epoch), 0, int(KeyLen), int(ValLen), 0, false, 0, int(TimeEpochMs))
		s.NetworkInit()
		s.StartProposers()
		s.Run()
	}
	for {
		time.Sleep(10 * time.Second)
	}
}

// registerProto: the real google.golang.org/protobuf needs no codec (the lab's protobuf model took
// the kit's generated codec here, proto.SetCodec; notes/dsv-quepaxa.md, "What is missing").
func registerProto() {}

// attempt is AttemptMs as a duration.
func attempt() time.Duration {
	return time.Duration(AttemptMs) * time.Millisecond
}

// orch is the orchestrator over the given configuration and client addresses: New, a wait of
// StartMs for the machines to connect (time is not modeled), then remote.Check of a random 1 to K
// operations per client.
func orch(cfgs []string, clients []string, gen func(int) any) {
	New(cfgs)
	time.Sleep(time.Duration(StartMs) * time.Millisecond)
	remote.Check(Model(), clients, Codec(), gen, 1+rand.Intn(int(K)), attempt())
}

// Orch is the orchestrator's program: it panics unless porcupine accepts the history of the
// clients' operations.
func Orch() {
	orch(CfgAddrs(), ClientAddrs(), Gens())
}

// clientNode is client machine c's program in the deployment at addrs with configuration addresses
// cfgs, served at req. Its QuePaxa client is made once, before serving (remote.ServeClient's
// newClient is a persistent triple with precondition True, and a second QuePaxa client of client
// c would listen at the same address again).
func clientNode(c uint64, addrs []string, cfgs []string, req string, checks bool) {
	s := newClient(addrs, cfgs, c, checks)
	newClient := func(id int) any {
		return s
	}
	op := func(sys any, in any) any {
		return Op(sys.(*Sys), in.(In))
	}
	remote.ServeClient(int(c), req, newClient, op, Codec(), attempt())
}

// Client is client machine c's program (c < NC). It never returns.
func Client(c uint64) {
	clientNode(c, Addrs(), CfgAddrs(), ClientAddrs()[c], false)
}

// Server is server machine id's program (1 <= id <= MaxReplicas). It never returns.
func Server(id uint64) {
	serve(id, Addrs(), RecAddrs(), CfgAddrs())
}
