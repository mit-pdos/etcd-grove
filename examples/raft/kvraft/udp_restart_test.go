package kvraft

import (
	"math/rand"
	"net"
	"strconv"
	"sync"
	"testing"
	"time"

	"go.etcd.io/raft/v3"
	pb "go.etcd.io/raft/v3/raftpb"
)

// freeUDPAddrs are n addresses of 127.0.0.1 whose UDP ports are free now, below Linux's ephemeral
// range (AddrOk).
func freeUDPAddrs(t *testing.T, n int) []string {
	var addrs []string
	var cs []*net.UDPConn
	defer func() {
		for _, c := range cs {
			c.Close()
		}
	}()
	for tries := 0; len(addrs) < n; tries++ {
		if tries > 1000 {
			t.Fatal("no free UDP port")
		}
		port := 20000 + rand.Intn(32768-20000)
		c, err := net.ListenUDP("udp4", &net.UDPAddr{IP: []byte{127, 0, 0, 1}, Port: port})
		if err != nil {
			continue
		}
		cs = append(cs, c)
		addrs = append(addrs, "127.0.0.1:"+strconv.Itoa(port))
	}
	return addrs
}

// udpCluster is replicas of one cluster in this test's process, each with its own UDP endpoint
// (its receiver running), started one by one.
type udpCluster struct {
	t     *testing.T
	cfg   NodeConfig // the cluster's: ID and Dir set per replica
	nodes map[uint64]*Node
	nets  map[uint64]*udpNet
	seq   uint64
}

func (c *udpCluster) start(id uint64) {
	cfg := c.cfg
	cfg.ID = id
	n, u := startNodeUDP(cfg)
	go u.receive(n)
	c.nodes[id], c.nets[id] = n, u
}

// put puts key=val through a random replica, retrying until one answers.
func (c *udpCluster) put(key, val string) {
	var ids []uint64
	for id := range c.nodes {
		ids = append(ids, id)
	}
	for try := 0; try < 200; try++ {
		c.seq++
		n := c.nodes[ids[rand.Intn(len(ids))]]
		if _, ok := n.handle(ReqPropose, EncodeOp(c.seq, OpPut, key, val), 300*time.Millisecond); ok {
			return
		}
	}
	c.t.Fatalf("Put %s not answered\n%s", key, c.dump())
}

// read reads key at replica id, retrying until it answers.
func (c *udpCluster) read(id uint64, key string) string {
	for try := 0; try < 100; try++ {
		c.seq++
		if v, ok := c.nodes[id].handle(ReqRead, EncodeRead(c.seq, key), 300*time.Millisecond); ok {
			return string(v)
		}
	}
	c.t.Fatalf("Read %s at %d not answered", key, id)
	return ""
}

// dump describes each replica's raft state and counters.
func (c *udpCluster) dump() string {
	s := ""
	for id, n := range c.nodes {
		st := n.status()
		s += "replica " + strconv.FormatUint(id, 10) + ": lead " + strconv.FormatUint(st.Lead, 10) +
			" term " + strconv.FormatUint(st.Term, 10) + " role " + strconv.FormatUint(st.Role, 10) +
			" commit " + strconv.FormatUint(st.Commit, 10) + " applied " + strconv.FormatUint(st.Index, 10) +
			"\n  " + FormatStats(st.Stats) + "\n"
	}
	return s
}

func (c *udpCluster) stats() [NumStats]uint64 {
	var s [NumStats]uint64
	for _, n := range c.nodes {
		v := n.stats.Snapshot()
		for i := range s {
			s[i] += v[i]
		}
	}
	return s
}

// TestUDPCluster runs three replicas over the UDP transport in this process (loopback; PreVote
// and CheckQuorum on, so that the late replica's campaigns, and the elections, slowed by the
// replicas' file writes, which the durable package serializes in one process, settle quickly): two
// start, take writes, and compact their logs; the third starts late, so that it catches up by a
// snapshot (sent, acknowledged); then replicas restart in their process (ReqDisrupt's restart:
// the endpoint, its receiver, the boot number and the sequence numbers outlive the incarnation)
// between writes, and every replica reads back every write.
func TestUDPCluster(t *testing.T) {
	if testing.Short() {
		t.Skip("short")
	}
	addrs := freeUDPAddrs(t, 3)
	dir := t.TempDir()
	c := &udpCluster{t: t, nodes: make(map[uint64]*Node), nets: make(map[uint64]*udpNet),
		cfg: NodeConfig{Dir: dir, Addrs: map[uint64]string{1: addrs[0], 2: addrs[1], 3: addrs[2]},
			Opts: Options{Voters: 3, PreVote: true, CheckQuorum: true, MaxSizePerMsg: 4 << 10, MaxCommittedSizePerReady: 4 << 10, MaxInflightMsgs: 4}}}
	c.start(1)
	c.start(2)
	// values long enough that the snapshots (the store and the operations' answers) take several
	// fragments
	val := func(i int) string { return "v" + strconv.Itoa(i) + string(make([]byte, 200)) }
	const writes = 60
	for i := 0; i < writes; i++ {
		c.put("k"+strconv.Itoa(i), val(i))
	}
	if s := c.stats(); s[StCompactions] == 0 {
		t.Logf("no compaction yet: %s", FormatStats(s))
	}
	c.start(3)
	for i := writes; i < writes+20; i++ {
		c.put("k"+strconv.Itoa(i), val(i))
	}
	rnd := rand.New(rand.NewSource(1))
	const restarts = 6
	for k := 0; k < restarts; k++ {
		id := uint64(1 + rnd.Intn(3))
		if _, ok := c.nodes[id].handle(ReqDisrupt, EncodeDisrupt(3, 0), time.Second); !ok {
			t.Fatalf("restart of %d not answered", id)
		}
		c.put("r"+strconv.Itoa(k), val(k))
	}
	for id := uint64(1); id <= 3; id++ {
		for i := 0; i < writes+20; i += 7 {
			if v := c.read(id, "k"+strconv.Itoa(i)); v != val(i) {
				t.Fatalf("replica %d: k%d = %q", id, i, v)
			}
		}
		for k := 0; k < restarts; k++ {
			if v := c.read(id, "r"+strconv.Itoa(k)); v != val(k) {
				t.Fatalf("replica %d: r%d = %q", id, k, v)
			}
		}
	}
	for id, u := range c.nets {
		if u.boot != 1 {
			t.Fatalf("replica %d: boot %d, want 1", id, u.boot)
		}
	}
	s := c.stats()
	t.Logf("%s", FormatStats(s))
	if s[StRestartsInProcess] != restarts || s[StUDPFragmentsSent] == 0 || s[StUDPMultiFragment] == 0 {
		t.Fatalf("restarts %d, fragments sent %d, multi-fragment messages %d", s[StRestartsInProcess],
			s[StUDPFragmentsSent], s[StUDPMultiFragment])
	}
	if s[StCompactions] != 0 && (s[StSnapshotsSent] == 0 || s[StUDPSnapshotsAcked] == 0) {
		t.Fatalf("compactions %d, snapshots sent %d, acked %d", s[StCompactions], s[StSnapshotsSent], s[StUDPSnapshotsAcked])
	}
	for _, n := range c.nodes {
		n.current().stop()
	}
}

// reportNode is a raft.Node that records the transport's reports (and nothing else is called).
type reportNode struct {
	raft.Node
	mu        sync.Mutex
	snapshots []raft.SnapshotStatus
}

func (r *reportNode) ReportUnreachable(id uint64) {}

func (r *reportNode) ReportSnapshot(id uint64, status raft.SnapshotStatus) {
	r.mu.Lock()
	r.snapshots = append(r.snapshots, status)
	r.mu.Unlock()
}

func (r *reportNode) reports() []raft.SnapshotStatus {
	r.mu.Lock()
	defer r.mu.Unlock()
	return append([]raft.SnapshotStatus(nil), r.snapshots...)
}

// TestUDPSnapshotReports checks a snapshot's reports: finished once its receiver acknowledges it
// (a replica's receiver, acking what it completes; the sender's receiver routing the ack), and
// failed, after snapResends resends, when nothing acknowledges it (a socket that only reads).
func TestUDPSnapshotReports(t *testing.T) {
	addrs := freeUDPAddrs(t, 3)
	cfg := NodeConfig{ID: 1, Dir: t.TempDir(), Addrs: map[uint64]string{1: addrs[0], 2: addrs[1], 3: addrs[2]},
		Opts: Options{Voters: 1, MaxSizePerMsg: 4 << 10, MaxCommittedSizePerReady: 4 << 10, MaxInflightMsgs: 4}}
	// replica 2: a single-voter replica whose receiver acks the snapshots it completes
	cfg2 := cfg
	cfg2.ID = 2
	n2, u2 := startNodeUDP(cfg2)
	go u2.receive(n2)
	defer n2.current().stop()
	// replica 3: a socket that reads and never answers
	ua3, _ := udpAddr(addrs[2])
	sink := listenUDP(ua3)
	defer sink.Close()
	go func() {
		buf := make([]byte, maxDatagram)
		for {
			if _, _, err := sink.ReadFromUDP(buf); err != nil {
				return
			}
		}
	}()
	// replica 1: a replica (its receiver routes the acks), and beside its own transport, the one
	// under test, over the same endpoint, reporting to a recording node
	n1, u := startNodeUDP(cfg)
	go u.receive(n1)
	defer n1.current().stop()
	stats := &Stats{}
	tr := u.newTransport(1, cfg.Addrs, stats).(*udpTransport)
	node := &reportNode{}
	tr.start(node)
	defer tr.stop()
	snap := func(to uint64) *pb.Message {
		data := make([]byte, 3*chunkSize)
		return &pb.Message{Type: pb.MsgSnap.Enum(), To: new(to), From: new(uint64(1)), Term: new(uint64(1)),
			Snapshot: &pb.Snapshot{Data: data, Metadata: &pb.SnapshotMetadata{Index: new(uint64(5)), Term: new(uint64(1)),
				ConfState: &pb.ConfState{Voters: []uint64{1}}}}}
	}
	tr.Send([]*pb.Message{snap(2), snap(3)})
	deadline := time.Now().Add(snapAckWait*(snapResends+1) + 3*time.Second)
	for len(node.reports()) < 2 && time.Now().Before(deadline) {
		time.Sleep(10 * time.Millisecond)
	}
	rs := node.reports()
	s := stats.Snapshot()
	t.Logf("reports %v; %s; replica 2: %s", rs, FormatStats(s), FormatStats(n2.stats.Snapshot()))
	if len(rs) != 2 || rs[0] != raft.SnapshotFinish || rs[1] != raft.SnapshotFailure {
		t.Fatalf("reports %v, want [finish failure]", rs)
	}
	if s[StUDPSnapshotsAcked] != 1 || s[StUDPSnapshotsFailed] != 1 || s[StUDPSnapshotResends] < snapResends {
		t.Fatalf("acked %d, failed %d, resends %d", s[StUDPSnapshotsAcked], s[StUDPSnapshotsFailed], s[StUDPSnapshotResends])
	}
	if a := n2.stats.Snapshot()[StUDPAcksSent]; a == 0 {
		t.Fatal("replica 2 sent no ack")
	}
}
