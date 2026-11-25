// Package epaxosnet is the EPaxos kit (dsverify-lab's epaxos-e1nogs-1, notes/dsv-epaxos.md) as an
// instance of examples/lib/remote: SwiftPaxos's EPaxos (the lab's fork, commit 71d99d4) over TCP
// (Go's net, net/rpc and net/http), a key-value store with scans whose clients each run on a
// machine of their own, checked by porcupine on an orchestrator machine. Seventeen machines, each
// a command of cmd/:
//
//   - the orchestrator (Orch): remote.Check of NC clients' operations, Ops each, made at the
//     clients' own machines, against the store with scans and pending writes (Model);
//   - client machine c (Client, c < NC): remote.ServeClient whose operation is one SwiftPaxos
//     command on a connection of its own to the replica Server(2 + c mod NReplicas) (Op);
//   - server machine 1 (Server(1)): SwiftPaxos's master (runMaster);
//   - server machine id (Server(id), 2 <= id <= NReplicas+1): an EPaxos replica (runReplica): it
//     registers with the master over net/rpc until the master is ready, then runs epaxos.New
//     with the id and node list the master returns, and serves net/rpc over HTTP.
//
// An operation that fails or is never answered has an unknown outcome (Out{Unknown: true}).
//
// (dsverify-lab's kit generated its configuration, Main and ClientNode with kitgen and checked
// the history with its own driver, recorder and checker; here they are remote's, lintest's and
// porcupine's, and the model is this package's.)
package epaxosnet

import (
	"bufio"
	"encoding/binary"
	"math/rand"
	"net"
	"net/http"
	"net/rpc"
	"time"

	"github.com/goose-lang/primitive"
	"github.com/imdea-software/swiftpaxos-epaxos/config"
	"github.com/imdea-software/swiftpaxos-epaxos/dlog"
	"github.com/imdea-software/swiftpaxos-epaxos/epaxos"
	"github.com/imdea-software/swiftpaxos-epaxos/master"
	"github.com/imdea-software/swiftpaxos-epaxos/replica/defs"
	"github.com/imdea-software/swiftpaxos-epaxos/state"
	"github.com/mit-pdos/etcd-grove/examples/lib/remote"
)

// The configuration: NC clients, Ops operations each, NReplicas replicas, NKeys keys, a scan's
// range (ScanN: keys k..k+ScanN), how long a client waits before its first operation (StartMs:
// the replicas' start-up), and then a replica's clients StaggerMs after the previous replica's,
// a dial's limit, the replicas' wait between registrations, and one remote call's limit.
const (
	NC         uint64 = 10
	Ops        uint64 = 2
	NReplicas  uint64 = 5
	NKeys      uint64 = 2
	ScanN      uint64 = 1
	StartMs    uint64 = 20000
	StaggerMs  uint64 = 300
	DialMs     uint64 = 3000
	RegisterMs uint64 = 100
	AttemptMs  uint64 = 45000
)

// ServerAddrs is the server machines' addresses: server id at index id-1 (the master, then the
// replicas). Server id listens at its port (the master: on every interface, as SwiftPaxos's
// master does); a replica's net/rpc server 1000 above it.
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

// Port0 is server id's port less id.
const Port0 uint64 = 7500

// ClientAddrs is the client machines' addresses for the orchestrator's calls (remote.Serve).
func ClientAddrs() []string {
	return []string{
		"127.0.0.1:7511",
		"127.0.0.1:7512",
		"127.0.0.1:7513",
		"127.0.0.1:7514",
		"127.0.0.1:7515",
		"127.0.0.1:7516",
		"127.0.0.1:7517",
		"127.0.0.1:7518",
		"127.0.0.1:7519",
		"127.0.0.1:7520",
	}
}

func digit(n uint64) string {
	return string([]byte{byte('0' + n%10)})
}

// Gen is client c's next input, at random: a put of a random key with value "v<c><d>" (d a
// random digit: never empty, all of one length, so that a scan's concatenation is short to
// check), or a read of a random key: a get for the first NReplicas clients, a scan of ScanN+1 keys
// for the others (keys up to NKeys-1+ScanN: one never written). A replica's two clients (c and
// c+NReplicas) send it commands of both kinds.
func Gen(c int) any {
	n := primitive.RandomUint64()
	k := (n / 2) % NKeys
	if n%2 == 0 {
		return In{Op: OpPut, K: k, N: 0, V: "v" + digit(uint64(c)) + digit(n/(2*NKeys))}
	}
	if uint64(c) < NReplicas {
		return In{Op: OpGet, K: k, N: 0, V: ""}
	}
	return In{Op: OpScan, K: k, N: ScanN, V: ""}
}

// Op is client c's operation in on a connection of its own to the replica Server(2 + c mod
// NReplicas), as SwiftPaxos's client sends a command and reads its reply (client.SendProposal,
// GetReplyFrom): a PROPOSE byte and the marshaled defs.Propose (ClientId c) through a
// bufio.Writer, then a defs.ProposeReplyTS from a bufio.Reader, with no deadline (an operation
// never answered is the orchestrator's: its remote call gives up after AttemptMs, an unknown
// outcome). A put is a PUT command (client.SendWrite); a get a GET (SendRead), whose reply value
// is the key's value (empty: none); a scan of N from K a SCAN (SendScan: V is N as 8
// little-endian bytes), whose reply value is the values of the keys K..K+N present, in key order,
// concatenated (state.Command.Execute). An unknown outcome on any error or another reply.
func Op(addrs []string, c uint64, x In) Out {
	conn, err := net.DialTimeout("tcp", addrs[1+c%NReplicas], time.Duration(DialMs)*time.Millisecond)
	if err != nil {
		return Out{Unknown: true}
	}
	cmd := state.Command{Op: state.GET, K: state.Key(x.K), V: state.NIL()}
	if x.Op == OpPut {
		cmd = state.Command{Op: state.PUT, K: state.Key(x.K), V: state.Value([]byte(x.V))}
	} else if x.Op == OpScan {
		v := make([]byte, 8)
		binary.LittleEndian.PutUint64(v, x.N)
		cmd = state.Command{Op: state.SCAN, K: state.Key(x.K), V: state.Value(v)}
	}
	p := defs.Propose{CommandId: 0, ClientId: int32(c), Command: cmd, Timestamp: 0}
	w := bufio.NewWriter(conn)
	w.WriteByte(defs.PROPOSE)
	p.Marshal(w)
	if err := w.Flush(); err != nil {
		conn.Close()
		return Out{Unknown: true}
	}
	rep := &defs.ProposeReplyTS{}
	err2 := rep.Unmarshal(bufio.NewReader(conn))
	conn.Close()
	if err2 != nil || rep.OK != defs.TRUE || rep.CommandId != 0 {
		return Out{Unknown: true}
	}
	if x.Op == OpPut {
		return Out{V: ""}
	}
	return Out{V: string(rep.Value)}
}

// start is client c's delay before its first operation, drawn at each call: every client waits
// for the replicas to register, connect and finish their start-up (StartMs), then a random 0 to
// NReplicas*StaggerMs (time is not modeled: the theorem allows any delay).
func start(c uint64) time.Duration {
	return time.Duration(StartMs+uint64(rand.Intn(int(NReplicas*StaggerMs)+1))) * time.Millisecond
}

// attempt is AttemptMs as a duration.
func attempt() time.Duration {
	return time.Duration(AttemptMs) * time.Millisecond
}

// Orch is the orchestrator's program: it draws each client's number of operations, 1 to Ops, and
// panics unless porcupine accepts the history of the clients' operations.
func Orch() {
	remote.Check(Model(), ClientAddrs(), Codec(), Gen, 1+rand.Intn(int(Ops)), attempt())
}

// Client is client machine c's program (c < NC): remote.ServeClient whose system is the server
// addresses and whose operation is Op, none before start(c).
func Client(c uint64) {
	addrs := ServerAddrs()
	newClient := func(id int) any {
		return addrs
	}
	// The first operation waits until start(c) after the machine's start (the op closure reads
	// t0 only: no state written between its calls, as its verification wants; notes/dsv-epaxos.md).
	t0 := time.Now()
	op := func(sys any, in any) any {
		if d := start(c) - time.Since(t0); d > 0 {
			time.Sleep(d)
		}
		return Op(sys.([]string), c, in.(In))
	}
	remote.ServeClient(int(c), ClientAddrs()[c], newClient, op, Codec(), attempt())
}

// Server is server machine id's program (1 <= id <= NReplicas+1). It never returns (but on a
// failed rpc.Register or Listen).
func Server(id uint64) {
	serve(id, ServerAddrs(), Port0)
}

// nodeConfig is node id's configuration as SwiftPaxos's config.Read gives it for a config file
// with no proxies and no leader (no quorum, latency or log file: defs.LatencyConf stays "").
func nodeConfig(id uint64, port int) *config.Config {
	return &config.Config{
		Protocol: "epaxos",
		Alias:    "n" + digit(id),
		Port:     port,
		Leader:   nil,
		Proxy:    &config.ProxyInfo{},
	}
}

// register is runReplica's registerWithMaster: it registers (ip, port) with the master at maddr
// until the master says it is ready, and returns the replica's id and the replicas' addresses.
// Unlike runReplica's, it dials again after a failed call (runReplica retries the same client,
// which fails forever once its connection broke) and waits RegisterMs between calls (runReplica
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
				time.Sleep(time.Duration(RegisterMs) * time.Millisecond)
			}
			mcli.Close()
		}
		time.Sleep(time.Duration(RegisterMs) * time.Millisecond)
	}
}

// host is addr's host part (addr is "host:port").
func host(addr string) string {
	for i := len(addr) - 1; i >= 0; i-- {
		if addr[i] == ':' {
			return addr[:i]
		}
	}
	return addr
}

// serve is server id's program in the deployment at addrs (server id at addrs[id-1], listening
// at port0+id): the master (id 1), or a replica. The logger is SwiftPaxos's non-verbose
// dlog.Logger (dlog.New(path, false) less the log file it never writes): no output, and its Fatal
// does not exit.
func serve(id uint64, addrs []string, port0 uint64) {
	Register()
	port := int(port0 + id)
	cfg := nodeConfig(id, port)
	if id == 1 {
		m := master.New(int(NReplicas), port, cfg, &dlog.Logger{})
		m.Run()
		return
	}
	ip := host(addrs[id-1])
	replicaId, nodeList := register(ip, port, addrs[0])
	rep := epaxos.New(cfg.Alias, replicaId, nodeList, true, false, false, 0, false,
		int((NReplicas-1)/2), cfg, &dlog.Logger{})
	if err := rpc.Register(rep); err != nil {
		return
	}
	rpc.HandleHTTP()
	l, err := net.Listen("tcp", ip+":"+string(itoa(uint64(port+1000))))
	if err != nil {
		return
	}
	http.Serve(l, nil)
}

// itoa is n in decimal.
func itoa(n uint64) []byte {
	if n == 0 {
		return []byte{'0'}
	}
	var b []byte
	for n > 0 {
		b = append([]byte{byte('0' + n%10)}, b...)
		n /= 10
	}
	return b
}
