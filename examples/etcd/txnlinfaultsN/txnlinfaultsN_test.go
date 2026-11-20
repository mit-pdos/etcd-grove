package txnlinfaultsN

import (
	"context"
	"fmt"
	"math/rand"
	"os"
	"strconv"
	"strings"
	"sync"
	"testing"
	"time"

	"github.com/anishathalye/porcupine"
	"go.etcd.io/etcd/client/pkg/v3/types"
	clientv3 "go.etcd.io/etcd/client/v3"
	"go.etcd.io/etcd/server/v3/etcdserver/api/membership"
	"go.uber.org/zap"
	"go.uber.org/zap/zapcore"

	"github.com/mit-pdos/etcd-grove/examples/etcd/partition"
	"github.com/mit-pdos/etcd-grove/examples/lib/cluster3"
	"github.com/mit-pdos/etcd-grove/examples/lib/etcdstart"
	"github.com/mit-pdos/etcd-grove/examples/lib/walarea"
)

// maxMembers is the bound of etcd_txnlinfaultsN_safe's member count.
const maxMembers = 1000

// idsOf returns the member ids etcd computes for Main(k)'s cluster (from the peer URLs and the
// cluster token, as bootstrap does), without starting it.
func idsOf(t *testing.T, k uint64) []types.ID {
	ms := etcdstart.Members("txnlinfaultsN", k, PeerBase, ClientBase)
	urls := types.URLsMap{}
	for _, m := range ms {
		u, err := types.NewURLs([]string{"http://" + m.Peer})
		if err != nil {
			t.Fatal(err)
		}
		urls[m.Name] = u
	}
	cl, err := membership.NewClusterFromURLsMap(zap.NewNop(), Token, urls)
	if err != nil {
		t.Fatal(err)
	}
	return cl.MemberIDs()
}

// TestMemberIDs checks etcd_txnlinfaultsN_safe's premise on the member ids (BootCore: their 16 low
// bits distinct and not 0, D21e (A)) for every member count 1 <= k <= maxMembers, from the ids
// etcd computes for Main(k)'s cluster. It starts no cluster.
func TestMemberIDs(t *testing.T) {
	for k := uint64(1); k <= maxMembers; k++ {
		ids := idsOf(t, k)
		if uint64(len(ids)) != k {
			t.Fatalf("k=%d: %d ids", k, len(ids))
		}
		seen := map[uint64]bool{}
		for _, id := range ids {
			low := uint64(id) & 0xffff
			if low == 0 || seen[low] {
				t.Fatalf("k=%d: member %x: low 16 bits %#x zero or repeated", k, uint64(id), low)
			}
			seen[low] = true
		}
	}
}

// TestAddrs checks the members' and bridges' addresses at k = 3.
func TestAddrs(t *testing.T) {
	ms := etcdstart.Members("txnlinfaultsN", 3, PeerBase, ClientBase)
	for i, m := range ms {
		want := etcdstart.Member{
			Name:   fmt.Sprintf("txnlinfaultsN-%d", i),
			Peer:   fmt.Sprintf("127.0.0.1:%d", 26000+i),
			Client: fmt.Sprintf("127.0.0.1:%d", 27000+i),
		}
		if m != want {
			t.Fatalf("member %d: got %v, want %v", i, m, want)
		}
		if b := bridgeAddr(uint64(i)); b != fmt.Sprintf("127.0.0.1:%d", 28000+i) {
			t.Fatalf("bridge %d: got %s", i, b)
		}
	}
}

// isolate returns the steps that, after delay, cut member m from the k-1 others.
func isolate(delay time.Duration, k int, m int) []cluster3.Step {
	var steps []cluster3.Step
	for o := 0; o < k; o++ {
		if o != m {
			steps = append(steps, cluster3.Step{Delay: delay, Kind: cluster3.PeerCut, A: m, B: o})
			delay = 0
		}
	}
	return steps
}

// heal returns the steps that, after delay, mend member m's links to the k-1 others.
func heal(delay time.Duration, k int, m int) []cluster3.Step {
	var steps []cluster3.Step
	for o := 0; o < k; o++ {
		if o != m {
			steps = append(steps, cluster3.Step{Delay: delay, Kind: cluster3.PeerMend, A: m, B: o})
			delay = 0
		}
	}
	return steps
}

// schedule is TestMainRun's schedule for k members (partition's TestMainRun's, over k members):
// after half a second, each member isolated in turn for three seconds, back to back; during the
// first isolation the last member's clients blackholed, and as it ends that unblackholed and
// member (1 mod k)'s client connections dropped. (At k = 1 the peer steps are empty: a member
// has no link to cut; the client steps remain.)
func schedule(k int) []cluster3.Step {
	var sched []cluster3.Step
	for m := 0; m < k; m++ {
		delay := time.Duration(0)
		if m == 0 {
			delay = 500 * time.Millisecond
		}
		iso := isolate(delay, k, m)
		sched = append(sched, iso...)
		if m == 0 {
			if len(iso) > 0 {
				delay = 0
			}
			sched = append(sched, cluster3.Step{Delay: delay, Kind: cluster3.ClientBlackhole, A: k - 1})
		}
		sched = append(sched, heal(3*time.Second, k, m)...)
		if m == 0 {
			if k == 1 {
				sched = append(sched, cluster3.Step{Delay: 3 * time.Second})
			}
			sched = append(sched, cluster3.Step{Kind: cluster3.ClientUnblackhole, A: k - 1},
				cluster3.Step{Kind: cluster3.ClientDrop, A: 1 % k})
		}
	}
	return sched
}

// TestMainRun runs Main's body for real, once, for one member count k drawn at random from
// {1, 3, 5, 7} (TXNLINFAULTSN_MEMBERS=<k> overrides it), logged first so that a failure can be
// rerun: k members in a fresh directory (the members' DataDirs are relative), 3 clients of 150
// operations each, on schedule(k). It runs startCluster, the partitioner, partition.Check and the
// panic on Illegal with a logger that counts what the members did (runCounts), where Main has
// none. Porcupine's verdict must be Ok. Then it asks each member, which Main left running, for the
// keys (so that the history was not all errors, and the members, mended, agree) and the member
// count. With more than one member, the run must also have tested what partition's does: a leader
// change (each member, the leader too, is isolated once), a follower caught up by entries, raft's
// log compacted and a snapshot sent to a follower.
func TestMainRun(t *testing.T) {
	ks := []uint64{1, 3, 5, 7}
	k := ks[rand.Intn(len(ks))]
	if s := os.Getenv("TXNLINFAULTSN_MEMBERS"); s != "" {
		v, err := strconv.ParseUint(s, 10, 64)
		if err != nil || v < 1 || v > maxMembers {
			t.Fatalf("TXNLINFAULTSN_MEMBERS=%q: not a member count in 1..%d", s, maxMembers)
		}
		k = v
	}
	t.Logf("txnlinfaultsN: k=%d (rerun with TXNLINFAULTSN_MEMBERS=%d)", k, k)
	t.Chdir(t.TempDir())
	walarea.ResetFamily(t, "txnlinfaultsN") // the members' WAL areas (wal-link P2)
	sched := schedule(int(k))

	start := time.Now()
	rc := newRunCounts()
	// Main's body, with rc's logger
	srvs, brs, clis, ok := startCluster(k, zap.New(rc))
	if !ok {
		t.Fatal("the cluster did not start")
	}
	go cluster3.Partitioner(srvs, brs, sched)
	r := partition.Check(clis, 3, 150, 0)
	if r == porcupine.Illegal {
		panic("txnlinfaultsN: porcupine found the history not linearizable")
	}
	if r != porcupine.Ok {
		t.Fatalf("got %v", r)
	}
	t.Logf("Main took %v", time.Since(start))
	t.Log(rc.report())
	if k > 1 {
		if n := rc.get(cntLeader); n < 2 {
			t.Errorf("%d leaders elected: no leader change", n)
		}
		if rc.get(cntAppReject) == 0 {
			t.Errorf("no follower was caught up by entries (no MsgApp rejected)")
		}
		if rc.get(cntCompact) == 0 {
			t.Errorf("raft's log was never compacted (SnapCount %d, SnapCatchUp %d)", SnapCount,
				SnapCatchUp)
		}
		if rc.get(cntSnapSent) == 0 {
			t.Errorf("no snapshot was sent (SnapCount %d, SnapCatchUp %d)", SnapCount, SnapCatchUp)
		}
	}

	// the schedule ended (every link mended) before the members are compared
	time.Sleep(time.Until(start.Add(time.Duration(k)*3*time.Second + 5*time.Second)))
	var kvs string
	for i := uint64(0); i < k; i++ {
		addr := "127.0.0.1:" + strconv.FormatUint(ClientBase+i, 10)
		cli, err := clientv3.New(clientv3.Config{Endpoints: []string{addr}, Logger: zap.NewNop()})
		if err != nil {
			t.Fatal(err)
		}
		ctx, cancel := context.WithTimeout(context.Background(), 10*time.Second)
		resp, err := cli.Get(ctx, "k", clientv3.WithPrefix())
		if err != nil {
			cancel()
			t.Fatalf("member %d: %v", i, err)
		}
		if resp.Header.Revision < 10 {
			t.Fatalf("member %d: Main's writes did not take effect: revision %d, %v", i,
				resp.Header.Revision, resp.Kvs)
		}
		s := ""
		for _, kv := range resp.Kvs {
			s += string(kv.Key) + "=" + string(kv.Value) + ";"
		}
		if i == 0 {
			kvs = s
		} else if s != kvs {
			t.Fatalf("member %d reads %q, member 0 %q", i, s, kvs)
		}
		ml, err := cli.MemberList(ctx)
		if err != nil {
			t.Fatal(err)
		}
		if uint64(len(ml.Members)) != k {
			t.Fatalf("expected %d members, got %d", k, len(ml.Members))
		}
		t.Logf("member %d: revision %d, raft term %d, keys %d", i, resp.Header.Revision,
			resp.Header.RaftTerm, len(resp.Kvs))
		cancel()
		cli.Close()
	}
}

// The events runCounts counts (partition's TestMainRun's), each by the message etcd or raft logs
// for it, summed over the members.
const (
	cntElection    = "is starting a new election"
	cntLeader      = "became leader at term"
	cntAppReject   = "rejected MsgApp ["
	cntCompact     = "compacted Raft logs"
	cntDiskSnap    = "saved snapshot to disk"
	cntSnapSent    = "sending merged snapshot"
	cntSnapApplied = "applied snapshot"
)

var cntEvents = []string{cntElection, cntLeader, cntAppReject, cntCompact, cntDiskSnap, cntSnapSent,
	cntSnapApplied}

// runCounts is a zap core that logs nothing and counts the messages of cntEvents, at every level.
type runCounts struct {
	mu *sync.Mutex
	n  map[string]int
}

func newRunCounts() runCounts { return runCounts{mu: &sync.Mutex{}, n: map[string]int{}} }

func (c runCounts) Enabled(zapcore.Level) bool        { return true }
func (c runCounts) With([]zapcore.Field) zapcore.Core { return c }
func (c runCounts) Sync() error                       { return nil }

func (c runCounts) Check(e zapcore.Entry, ce *zapcore.CheckedEntry) *zapcore.CheckedEntry {
	return ce.AddCore(e, c)
}

func (c runCounts) Write(e zapcore.Entry, _ []zapcore.Field) error {
	for _, k := range cntEvents {
		if strings.Contains(e.Message, k) {
			c.mu.Lock()
			c.n[k]++
			c.mu.Unlock()
		}
	}
	return nil
}

func (c runCounts) get(k string) int {
	c.mu.Lock()
	defer c.mu.Unlock()
	return c.n[k]
}

func (c runCounts) report() string {
	return fmt.Sprintf("run counts (summed over the members): elections started %d, leaders "+
		"elected %d; appends rejected by a lagging follower %d (each then caught up by entries); "+
		"log compactions %d, snapshots saved %d; snapshots sent %d, installed %d",
		c.get(cntElection), c.get(cntLeader), c.get(cntAppReject), c.get(cntCompact),
		c.get(cntDiskSnap), c.get(cntSnapSent), c.get(cntSnapApplied))
}
