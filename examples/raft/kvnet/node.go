package kvnet

import (
	"fmt"
	"net"
	"sync"
	"time"

	"github.com/mit-pdos/etcd-grove/examples/lib/durable"
	"go.etcd.io/raft/v3"
	pb "go.etcd.io/raft/v3/raftpb"
)

// quietLogger is a raft.Logger that discards what raft logs; Fatal and Panic panic, as raft
// expects of them (and the process then dies with the message on its standard error, which the
// driver reports).
type quietLogger struct{}

func (quietLogger) Debug(v ...interface{})                   {}
func (quietLogger) Debugf(format string, v ...interface{})   {}
func (quietLogger) Error(v ...interface{})                   {}
func (quietLogger) Errorf(format string, v ...interface{})   {}
func (quietLogger) Info(v ...interface{})                    {}
func (quietLogger) Infof(format string, v ...interface{})    {}
func (quietLogger) Warning(v ...interface{})                 {}
func (quietLogger) Warningf(format string, v ...interface{}) {}
func (quietLogger) Fatal(v ...interface{})                   { panic(fmt.Sprint(v...)) }
func (quietLogger) Fatalf(format string, v ...interface{})   { panic(fmt.Sprintf(format, v...)) }
func (quietLogger) Panic(v ...interface{})                   { panic(fmt.Sprint(v...)) }
func (quietLogger) Panicf(format string, v ...interface{})   { panic(fmt.Sprintf(format, v...)) }

// Options are a cluster's bootstrap size and raft's options, kvdurable's.
type Options struct {
	Voters                   uint64 // the bootstrap configuration's, 1 to 5: ids 1 to Voters
	PreVote                  bool
	CheckQuorum              bool
	StepDownOnRemoval        bool
	MaxSizePerMsg            uint64
	MaxCommittedSizePerReady uint64 // never 0 when MaxSizePerMsg is (raft panics with both 0)
	MaxInflightMsgs          int
}

// RandomOptions are options chosen at random, as kvdurable's.
func RandomOptions() Options {
	o := Options{
		Voters:            1 + below(5),
		PreVote:           oneIn(2),
		CheckQuorum:       oneIn(2),
		StepDownOnRemoval: oneIn(2),
		MaxSizePerMsg:     []uint64{0, 256, 4 << 10, 1 << 20}[below(4)],
		MaxInflightMsgs:   []int{1, 4, 256}[below(3)],
	}
	o.MaxCommittedSizePerReady = []uint64{0, 4 << 10, 1 << 20}[below(3)]
	if o.MaxSizePerMsg == 0 && o.MaxCommittedSizePerReady == 0 {
		o.MaxCommittedSizePerReady = 4 << 10
	}
	return o
}

// NodeConfig is what a replica's process is started with: its id, the directory of its durable
// file, the address of every replica the cluster may start (its own included: it listens there),
// and the cluster's options.
type NodeConfig struct {
	ID    uint64
	Dir   string
	Addrs map[uint64]string
	Opts  Options
}

// itoa is n in decimal.
func itoa(n uint64) string {
	if n == 0 {
		return "0"
	}
	var b []byte
	for n != 0 {
		b = append([]byte{byte('0' + n%10)}, b...)
		n = n / 10
	}
	return string(b)
}

// FileOf is the durable file of replica id in the directory dir.
func FileOf(dir string, id uint64) string {
	return dir + "/replica-" + itoa(id)
}

// Node is a running replica: its counters and, under mu, its current incarnation's replica and
// transport (restart replaces them; mu is held for the whole restart, so that two restarts never
// overlap and nothing uses a half-started incarnation).
type Node struct {
	cfg   NodeConfig
	stats *Stats
	newT  newPeerTransport
	mu    sync.Mutex
	r     *Replica
	t     peerTransport
}

// current is the current incarnation's replica.
func (n *Node) current() *Replica {
	n.mu.Lock()
	r := n.r
	n.mu.Unlock()
	return r
}

// stepPeer steps a message a peer sent (a transport received it) on the current incarnation's
// node; one the node does not take within stepTimeout is dropped (as is one stepped on an
// incarnation stopped meanwhile).
func (n *Node) stepPeer(m *pb.Message) {
	n.stats.add(StMsgsReceived)
	r := n.current()
	ctx, cancel := withTimeout(stepTimeout)
	r.node.Step(ctx, m)
	cancel()
}

// restart stops the current incarnation cleanly (Replica.stop: its loop, clock and snapshot
// goroutine, then raft's Node.Stop; then its transport's senders, Transport.stop) and starts the next one in this
// process from the file (start), as kvdurable's Cluster.restart does with a crash. What the
// stopped incarnation still holds in memory and never wrote is lost, as in a crash; requests
// waiting on it time out.
func (n *Node) restart() {
	n.mu.Lock()
	stopIncarnation(n.r, n.t)
	n.stats.add(StRestartsInProcess)
	n.r, n.t = start(n.cfg, n.stats, n.newT)
	n.mu.Unlock()
}

// listen listens on addr, retrying until it can (the previous incarnation's socket may not be
// gone yet): a failed Listen is never a panic (the net extension lets any Listen fail).
func listen(addr string) net.Listener {
	for {
		l, err := net.Listen("tcp", addr)
		if err == nil {
			return l
		}
		time.Sleep(10 * time.Millisecond)
	}
}

// RunNode is a replica's process, as the top-level theorem runs it: replica id of the cluster
// whose replicas' addresses are addrs (comma-separated, replica i at the i-th, ids from 1), its
// durable file in the directory dir, the bootstrap configuration's voters 1..voters, and raft's
// options. It returns at once, doing nothing, if the cluster is not one it can run (ValidCluster),
// id is not one of its replicas, or dir is too long (MaxDirLen): a configuration it cannot run is a
// safe run, so the top-level theorem needs no premise that the configuration is valid. Otherwise it
// never returns (Run).
func RunNode(id uint64, addrs string, dir string, voters uint64, preVote, checkQuorum, stepDownOnRemoval bool,
	maxSizePerMsg, maxCommittedSizePerReady, maxInflightMsgs uint64) {
	as := SplitAddrs(addrs)
	if !ValidCluster(as, voters, maxSizePerMsg, maxCommittedSizePerReady, maxInflightMsgs) ||
		id < 1 || id > uint64(len(as)) || uint64(len(dir)) >= MaxDirLen {
		return
	}
	m := make(map[uint64]string)
	for i, a := range as {
		m[uint64(i)+1] = a
	}
	Run(NodeConfig{ID: id, Dir: dir, Addrs: m, Opts: Options{
		Voters: voters, PreVote: preVote, CheckQuorum: checkQuorum, StepDownOnRemoval: stepDownOnRemoval,
		MaxSizePerMsg: maxSizePerMsg, MaxCommittedSizePerReady: maxCommittedSizePerReady,
		MaxInflightMsgs: int(maxInflightMsgs)}})
}

// Run runs the replica cfg.ID until its process ends: it starts it from its durable file
// (StartNode), then serves its peers and clients on its address. It never returns.
func Run(cfg NodeConfig) {
	l := listen(cfg.Addrs[cfg.ID])
	StartNode(cfg).accept(l)
}

// accept serves the connections l accepts, peers' and clients', each in a goroutine of its own
// (serve). It never returns.
func (n *Node) accept(l net.Listener) {
	for {
		c, err := l.Accept()
		if err != nil {
			// out of file descriptors, say: wait instead of spinning
			time.Sleep(10 * time.Millisecond)
			continue
		}
		go n.serve(c)
	}
}

// StartNode starts an incarnation of replica cfg.ID from its file, as kvdurable's Cluster.start
// does: its storage as the file left it (an empty one if there is no file: a replica that never
// wrote it, or wrote it only before a power loss took it away), its node restarted on it
// (raft.RestartNode), and its replicated state the storage's snapshot's (the empty state at the
// bootstrap configuration if it has none); Config.Applied is left 0 one time in three, or a
// random index from the log's start to the snapshot's, the entries up to the snapshot's index
// then being skipped (Replica.applyEntry).
func StartNode(cfg NodeConfig) *Node {
	return startNode(cfg, newTCPTransport)
}

// startNode is StartNode with the transport newT makes (its incarnations' each).
func startNode(cfg NodeConfig, newT newPeerTransport) *Node {
	stats := &Stats{}
	r, t := start(cfg, stats, newT)
	return &Node{cfg: cfg, stats: stats, newT: newT, r: r, t: t}
}

// stopIncarnation stops the incarnation of replica r and transport t (start's) for good: the
// replica (Replica.stop), then the transport's senders.
func stopIncarnation(r *Replica, t peerTransport) {
	r.stop()
	t.stop()
}

// start starts an incarnation of replica cfg.ID from its file (StartNode), with the transport newT
// makes, counting in stats.
func start(cfg NodeConfig, stats *Stats, newT newPeerTransport) (*Replica, peerTransport) {
	boot := &pb.ConfState{}
	for id := uint64(1); id <= cfg.Opts.Voters; id++ {
		boot.Voters = append(boot.Voters, id)
	}
	file := FileOf(cfg.Dir, cfg.ID)
	st := newStorage(boot)
	if data, ok := durable.Read(file); ok {
		s, good := openStorage(boot, []byte(data))
		if !good {
			panic("kvnet: a file this package did not write")
		}
		st = s
	}
	snap, _ := st.MemoryStorage.Snapshot()
	index := snap.GetMetadata().GetIndex()
	kv, ops, cs := make(map[string]string), make(map[string]string), boot
	if index != 0 {
		k, o, ok := decodeState(snap.GetData())
		if !ok {
			panic("kvnet: a snapshot whose data does not decode")
		}
		kv, ops, cs = k, o, snap.GetMetadata().GetConfState()
		stats.add(StRestartsFromSnapshot)
	}
	first, _ := st.FirstIndex()
	applied := uint64(0)
	rafted := first - 1
	if !oneIn(3) {
		applied = first - 1 + below(index-(first-1)+1)
		rafted = applied
	}
	if rafted < index {
		stats.add(StRestartsAppliedBelow)
	}
	t := newT(cfg.ID, cfg.Addrs, stats)
	node := raft.RestartNode(&raft.Config{
		ID:                       cfg.ID,
		ElectionTick:             10,
		HeartbeatTick:            1,
		Storage:                  st,
		Applied:                  applied,
		MaxSizePerMsg:            cfg.Opts.MaxSizePerMsg,
		MaxCommittedSizePerReady: cfg.Opts.MaxCommittedSizePerReady,
		MaxInflightMsgs:          cfg.Opts.MaxInflightMsgs,
		Logger:                   quietLogger{},
		PreVote:                  cfg.Opts.PreVote,
		CheckQuorum:              cfg.Opts.CheckQuorum,
		StepDownOnRemoval:        cfg.Opts.StepDownOnRemoval,
	})
	t.start(node)
	tick := time.Duration(1+below(4)) * time.Millisecond
	r := newReplica(cfg.ID, file, node, st, kv, ops, cs, index, rafted, tick, stats, t.Send)
	return r, t
}

// helloTimeout bounds how long a new connection may take to say what it is.
const helloTimeout = time.Second

// serve serves one accepted connection: a peer's (Transport.servePeer) or a client's
// (serveClient), by its first byte.
func (n *Node) serve(c net.Conn) {
	var hello [1]byte
	disarm := closeAfter(c, helloTimeout)
	read := readFull(c, hello[:])
	if !disarm() || !read {
		c.Close()
		return
	}
	switch hello[0] {
	case helloPeer:
		n.servePeer(c)
	case helloClient:
		n.serveClient(c)
	default:
		c.Close()
	}
}

// servePeer reads messages from a peer's connection and steps them on the current incarnation's
// node, until the connection fails or ends. A frame that does not decode, or a message not
// addressed to this replica, ends the connection.
func (n *Node) servePeer(c net.Conn) {
	defer c.Close()
	for {
		b, ok := readFrame(c)
		if !ok {
			return
		}
		m, good := getMsg(b)
		if !good || m.GetTo() != n.cfg.ID {
			n.stats.add(StBadFrames)
			return
		}
		n.stepPeer(m)
	}
}

// The client requests (the first byte of a request frame, after which comes the request's
// timeout in milliseconds, 8 bytes, then its payload).
const (
	ReqPropose = 1 // payload: an operation (encode); answer: its value
	ReqRead    = 2 // payload: a read's sequence number (8 bytes) and key (putBytes); answer: the value
	ReqConf    = 3 // payload: a configuration change (PutConfChange); answer: none
	ReqDisrupt = 4 // payload: what (8 bytes: 0 transfer, 1 campaign, 2 forget the leader, 3 restart the replica in its process), the transferee (8 bytes)
	ReqStatus  = 5 // answer: Status (PutStatus)
)

// maxReqTimeout bounds a request's timeout.
const maxReqTimeout = 10 * time.Second

// serveClient answers one request frame with one response frame: 1 (ok) and the answer, or 0
// (no answer: the client tries again, here or elsewhere).
func (n *Node) serveClient(c net.Conn) {
	defer c.Close()
	disarm := closeAfter(c, helloTimeout)
	b, ok := readFrame(c)
	if !disarm() || !ok || len(b) < 9 {
		return
	}
	ms, payload, _ := getUint64(b[1:])
	timeout := time.Duration(ms) * time.Millisecond
	if timeout > maxReqTimeout {
		timeout = maxReqTimeout
	}
	ans, good := n.handle(b[0], payload, timeout)
	resp := []byte{0}
	if good {
		resp = append([]byte{1}, ans...)
	}
	disarmW := closeAfter(c, writeTimeout)
	writeFrame(c, resp)
	disarmW()
}

// handle runs one request; false if it has no answer.
func (n *Node) handle(kind byte, p []byte, timeout time.Duration) ([]byte, bool) {
	r := n.current()
	switch kind {
	case ReqPropose:
		if _, _, _, _, ok := decode(p); !ok {
			return nil, false
		}
		v, ok := r.propose(p, timeout)
		return []byte(v), ok
	case ReqRead:
		seq, r1, ok1 := getUint64(p)
		key, _, ok2 := getBytes(r1)
		if !ok1 || !ok2 {
			return nil, false
		}
		v, ok := r.read(seq, string(key), timeout)
		return []byte(v), ok
	case ReqConf:
		cc, ok := GetConfChange(p)
		if !ok {
			return nil, false
		}
		n.stats.add(StConfChangesProposed)
		ctx, cancel := withTimeout(timeout)
		err := r.node.ProposeConfChange(ctx, cc)
		cancel()
		return nil, err == nil
	case ReqDisrupt:
		what, r1, ok1 := getUint64(p)
		to, _, ok2 := getUint64(r1)
		if !ok1 || !ok2 {
			return nil, false
		}
		if what == 3 {
			n.restart()
			return nil, true
		}
		ctx, cancel := withTimeout(timeout)
		switch what {
		case 0:
			r.node.TransferLeadership(ctx, r.node.Status().Lead, to)
		case 1:
			r.node.Campaign(ctx)
		default:
			r.node.ForgetLeader(ctx)
		}
		cancel()
		return nil, true
	case ReqStatus:
		return PutStatus(nil, n.status()), true
	}
	return nil, false
}

// Status is what ReqStatus answers: the replica's replicated state (its applied index,
// configuration and store contents, read at once), its raft state, and its counters.
type Status struct {
	Index    uint64
	Conf     *pb.ConfState
	Contents map[string]string
	Lead     uint64
	Term     uint64
	Role     uint64 // raft.StateType
	Commit   uint64
	Stats    [NumStats]uint64
}

// status is the replica's Status now.
func (n *Node) status() Status {
	r := n.current()
	contents, index, cs := r.contents()
	st := r.node.Status()
	return Status{Index: index, Conf: cs, Contents: contents, Lead: st.Lead, Term: st.HardState.GetTerm(),
		Role: uint64(st.RaftState), Commit: st.HardState.GetCommit(), Stats: n.stats.Snapshot()}
}
