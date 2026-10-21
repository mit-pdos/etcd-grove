package linkv3p

import (
	"context"
	"math/rand"
	"os"
	"os/exec"
	"sync"
	"testing"
	"time"

	"github.com/anishathalye/porcupine"
	"go.etcd.io/etcd/client/pkg/v3/types"
	clientv3 "go.etcd.io/etcd/client/v3"
	"go.etcd.io/etcd/server/v3/etcdserver"
	"go.etcd.io/etcd/server/v3/etcdserver/api/membership"
	"go.uber.org/zap"

	"github.com/mit-pdos/etcd-grove/examples/linkvtxn"
	"github.com/mit-pdos/etcd-grove/examples/lintest"
	"github.com/mit-pdos/etcd-grove/third_party/bridge"
)

// TestMemberIDs checks D21e (A)'s premise on the member ids etcd computes for Main's cluster (from
// the peer URLs and the cluster token): their 16 low bits are distinct and not 0. It prints the
// ids in the order bootstrap sorts them (the proof's BootFacts).
func TestMemberIDs(t *testing.T) {
	urls, err := types.NewURLsMap("linkv3p-1=http://" + peerAddr1 + ",linkv3p-2=http://" + peerAddr2 +
		",linkv3p-3=http://" + peerAddr3)
	if err != nil {
		t.Fatal(err)
	}
	cl, err := membership.NewClusterFromURLsMap(zap.NewNop(), "linkv3p", urls)
	if err != nil {
		t.Fatal(err)
	}
	seen := map[uint64]bool{}
	for _, id := range cl.MemberIDs() {
		low := uint64(id) & 0xffff
		t.Logf("member %x (%s): low 16 bits %#x", uint64(id), cl.Member(id).Name, low)
		if low == 0 || seen[low] {
			t.Fatalf("member %x: low 16 bits %#x zero or repeated", uint64(id), low)
		}
		seen[low] = true
	}
}

// inChild runs the test name in a child process and reports whether it did (the caller then
// returns); in the child it returns false and the test runs. A test that starts members runs so:
// the members keep their ports until their process exits (Main does not stop them), so two such
// tests in one process would collide.
func inChild(t *testing.T, name string) bool {
	if os.Getenv("LINKV3P_CHILD") == name {
		return false
	}
	args := []string{"-test.run=^" + name + "$", "-test.v"}
	// the parent's deadline (go test's -timeout) less 30s, so that a hung child fails first,
	// with its stacks
	if d, ok := t.Deadline(); ok {
		args = append(args, "-test.timeout="+(time.Until(d)-30*time.Second).String())
	}
	cmd := exec.Command(os.Args[0], args...)
	cmd.Env = append(os.Environ(), "LINKV3P_CHILD="+name)
	out, err := cmd.CombinedOutput()
	t.Logf("%s", out)
	if err != nil {
		t.Fatal(err)
	}
	return true
}

// isolate returns the steps that, after delay, cut member m from the two others.
func isolate(delay time.Duration, m int) []Step {
	var steps []Step
	for o := 0; o < 3; o++ {
		if o != m {
			steps = append(steps, Step{Delay: delay, Kind: PeerCut, A: m, B: o})
			delay = 0
		}
	}
	return steps
}

// heal returns the steps that, after delay, mend member m's links to the two others.
func heal(delay time.Duration, m int) []Step {
	var steps []Step
	for o := 0; o < 3; o++ {
		if o != m {
			steps = append(steps, Step{Delay: delay, Kind: PeerMend, A: m, B: o})
			delay = 0
		}
	}
	return steps
}

// TestMainRun runs Main for real: three members in a fresh directory (the members' DataDirs are
// relative), 3 clients of 150 operations each, on a schedule that, after half a second, isolates
// each member in turn for three seconds, back to back (so the leader, whichever it is, is isolated
// once at least, its followers elect another and it steps down: CheckQuorum; an operation at an
// isolated member fails after the request timeout, 7s, and some member is isolated until the
// schedule ends, which stretches the workload over the schedule, as the re-election check needs).
// Few clients, since each fails about one operation per isolation, and a failed write stays
// pending in porcupine's model to the end of the history: with 8 clients, the check of a history
// took minutes now and then, once 35. The schedule also blackholes member 3's client during the
// first isolation and drops member 2's client connections as it ends. Porcupine's verdict must be
// Ok. Then it asks each member, which Main left running, for the keys (so that the history was not all errors, and the three members, mended, agree), the raft
// term (past the first election's: a re-election happened) and the member count. (The keys may
// all be deleted at the end: the workload has deletes; the revision says the writes took effect.)
func TestMainRun(t *testing.T) {
	if inChild(t, "TestMainRun") {
		return
	}
	t.Chdir(t.TempDir())
	var sched []Step
	for m := 0; m < 3; m++ {
		delay := time.Duration(0)
		if m == 0 {
			delay = 500 * time.Millisecond
		}
		sched = append(sched, isolate(delay, m)...)
		if m == 0 {
			sched = append(sched, Step{Kind: ClientBlackhole, A: 2})
		}
		sched = append(sched, heal(3*time.Second, m)...)
		if m == 0 {
			sched = append(sched, Step{Kind: ClientUnblackhole, A: 2}, Step{Kind: ClientDrop, A: 1})
		}
	}
	start := time.Now()
	if r := Main(3, 150, sched); r != porcupine.Ok {
		t.Fatalf("got %v", r)
	}
	t.Logf("Main took %v", time.Since(start))

	var kvs string
	for i, addr := range []string{clientAddr1, clientAddr2, clientAddr3} {
		cli, err := clientv3.New(clientv3.Config{Endpoints: []string{addr}, Logger: zap.NewNop()})
		if err != nil {
			t.Fatal(err)
		}
		ctx, cancel := context.WithTimeout(context.Background(), 10*time.Second)
		resp, err := cli.Get(ctx, "k", clientv3.WithPrefix())
		if err != nil {
			cancel()
			t.Fatalf("member %d: %v", i+1, err)
		}
		if resp.Header.Revision < 10 {
			t.Fatalf("member %d: Main's writes did not take effect: revision %d, %v", i+1,
				resp.Header.Revision, resp.Kvs)
		}
		if resp.Header.RaftTerm < 3 {
			t.Fatalf("member %d: raft term %d: no re-election happened", i+1, resp.Header.RaftTerm)
		}
		s := ""
		for _, kv := range resp.Kvs {
			s += string(kv.Key) + "=" + string(kv.Value) + ";"
		}
		if i == 0 {
			kvs = s
		} else if s != kvs {
			t.Fatalf("member %d reads %q, member 1 %q", i+1, s, kvs)
		}
		ml, err := cli.MemberList(ctx)
		if err != nil {
			t.Fatal(err)
		}
		if len(ml.Members) != 3 {
			t.Fatalf("expected 3 members, got %d", len(ml.Members))
		}
		t.Logf("member %d: revision %d, raft term %d, keys %d", i+1, resp.Header.Revision,
			resp.Header.RaftTerm, len(resp.Kvs))
		cancel()
		cli.Close()
	}
}

// An operation of TestClientCuts' run: the client it went through, when it started and ended
// (since the run's start), and whether it failed.
type cutOp struct {
	cli        int
	start, end time.Duration
	err        bool
}

// cutSetup starts Main's pieces for TestClientCuts and TestFailover: the three members, a bridge
// to each, and three clients, client i to the bridges eps(i); every client warmed up (a leader
// elected, gRPC's lazy connections made: a connection begun during a blackhole never completes
// its handshake, so its calls only wait, WaitForReady, and succeed after the unblackhole; the
// first election may fail a call, "leader changed").
func cutSetup(t *testing.T, eps func(i int) []string) ([]*etcdserver.EtcdServer, []bridge.Bridge,
	[]*clientv3.Client) {
	t.Helper()
	t.Chdir(t.TempDir())
	lg := zap.NewNop()
	peer := []types.URLs{{{Scheme: "http", Host: peerAddr1}}, {{Scheme: "http", Host: peerAddr2}},
		{{Scheme: "http", Host: peerAddr3}}}
	cluster := types.URLsMap{"linkv3p-1": peer[0], "linkv3p-2": peer[1], "linkv3p-3": peer[2]}
	peerAddrs := []string{peerAddr1, peerAddr2, peerAddr3}
	clientAddrs := []string{clientAddr1, clientAddr2, clientAddr3}
	var srvs []*etcdserver.EtcdServer
	var brs []bridge.Bridge
	var clis []*clientv3.Client
	for i := 0; i < 3; i++ {
		s, err := startMember([]string{"linkv3p-1", "linkv3p-2", "linkv3p-3"}[i], peer[i],
			peerAddrs[i], clientAddrs[i], cluster, lg)
		if err != nil {
			t.Fatal(err)
		}
		srvs = append(srvs, s)
	}
	for i := 0; i < 3; i++ {
		br, err := startBridge(bridgeAddrs[i], clientAddrs[i])
		if err != nil {
			t.Fatal(err)
		}
		brs = append(brs, br)
	}
	for i := 0; i < 3; i++ {
		cli, err := newClient(eps(i), lg)
		if err != nil {
			t.Fatal(err)
		}
		clis = append(clis, cli)
	}
	for i, cli := range clis {
		deadline := time.Now().Add(30 * time.Second)
		for {
			ctx, cancel := context.WithTimeout(context.Background(), 5*time.Second)
			_, err := cli.Get(ctx, "warmup")
			cancel()
			if err == nil {
				break
			}
			if time.Now().After(deadline) {
				t.Fatalf("client %d: %v", i+1, err)
			}
			time.Sleep(100 * time.Millisecond)
		}
	}
	return srvs, brs, clis
}

// cutRun runs linkvtxn's workload (3 workers of n operations each, each operation after a pause
// of pause) through the clients clis, each operation through one picked at random, with the
// partitioner on sched and, if control is not nil, control on its own goroutine (given the
// operations so far and the time since the run's start); it checks porcupine's verdict is Ok and
// returns the operations.
func cutRun(t *testing.T, srvs []*etcdserver.EtcdServer, brs []bridge.Bridge,
	clis []*clientv3.Client, sched []Step, n int, pause time.Duration,
	control func(snap func() []cutOp, since func() time.Duration)) []cutOp {
	t.Helper()
	var mu sync.Mutex
	var ops []cutOp
	t0 := time.Now()
	apply := func(input any) any {
		time.Sleep(pause)
		mu.Lock()
		i := rand.Intn(len(clis))
		mu.Unlock()
		start := time.Since(t0)
		out := linkvtxn.Apply(clis[i], input)
		end := time.Since(t0)
		mu.Lock()
		ops = append(ops, cutOp{i, start, end, out.(linkvtxn.Output).Err})
		mu.Unlock()
		return out
	}
	go partitioner(srvs, brs, sched)
	if control != nil {
		snap := func() []cutOp {
			mu.Lock()
			defer mu.Unlock()
			return append([]cutOp(nil), ops...)
		}
		go control(snap, func() time.Duration { return time.Since(t0) })
	}
	if r := lintest.Run(linkvtxn.Model(), apply, linkvtxn.Gen, lintest.CounterClock(), 3, n,
		0); r != porcupine.Ok {
		t.Fatalf("got %v", r)
	}
	t.Logf("the run took %v", time.Since(t0))
	nOk, nErr := [3]int{}, [3]int{}
	for _, op := range ops {
		if op.err {
			nErr[op.cli]++
		} else {
			nOk[op.cli]++
		}
	}
	t.Logf("operations per client: succeeded %v, failed %v", nOk, nErr)
	if nOk[0]+nOk[1]+nOk[2] == 0 {
		t.Fatalf("every operation failed")
	}
	return ops
}

// The bridges' addresses, by member.
var bridgeAddrs = []string{bridgeAddr1, bridgeAddr2, bridgeAddr3}

// TestClientCuts shows the clients' cuts and recovery at the same member (notes/client-cut-plan.md,
// D-C5): each client of one member's bridge, on a schedule that drops member 2's client
// connections at 20ms and 50ms and blackholes member 1's client from 0.1s to 3.1s. It checks:
// porcupine's verdict is Ok; some operation through client 1 failed (a call in flight during the
// blackhole hangs, and the unblackhole closes its connection: Unavailable; the clients are
// connected first, warmed up); some operation through client 1 that started after the
// unblackhole succeeded (gRPC re-dialed the bridge); and the history is not all errors.
// It runs 3 workers of 600 operations each (few workers, as TestMainRun's few clients: each worker
// fails about one operation per cut, and porcupine's check is exponential in the failed writes;
// with 6 workers of 1000, a check took a minute and a half now and then). It runs in a child
// process (inChild), as TestMainRun.
func TestClientCuts(t *testing.T) {
	if inChild(t, "TestClientCuts") {
		return
	}
	srvs, brs, clis := cutSetup(t, func(i int) []string { return []string{bridgeAddrs[i]} })
	// the drops first, while every worker runs; then the blackhole, which soon holds every worker
	// (each picks client 1 sooner or later), so the run outlasts it however fast operations are
	const blackholeAt, unblackholeAt = 100 * time.Millisecond, 3100 * time.Millisecond
	sched := []Step{
		{Delay: 20 * time.Millisecond, Kind: ClientDrop, A: 1},
		{Delay: 30 * time.Millisecond, Kind: ClientDrop, A: 1},
		{Delay: blackholeAt - 50*time.Millisecond, Kind: ClientBlackhole, A: 0},
		{Delay: unblackholeAt - blackholeAt, Kind: ClientUnblackhole, A: 0},
	}
	ops := cutRun(t, srvs, brs, clis, sched, 600, 0, nil)
	var failed1, okAfter1 bool
	for _, op := range ops {
		if op.cli == 0 && op.err {
			failed1 = true
		}
		if op.cli == 0 && !op.err && op.start > unblackholeAt {
			okAfter1 = true
		}
	}
	if !failed1 {
		t.Fatalf("no operation through client 1 failed: the blackhole cut nothing")
	}
	if !okAfter1 {
		t.Fatalf("no operation through client 1 succeeded after the unblackhole: no recovery")
	}
}

// TestFailover shows failover on a silent partition and the clients' return to the mended member
// (notes/keepalive-plan.md, D-KA4): every client of all three bridges, as Main's, in two phases
// that a control goroutine drives (each client finds a cut on its own, so the phases' times are
// not known in advance).
//
// Failover: member 1's bridge is blackholed at 50ms. A call on a client's connection to member 1
// hangs until the client's keepalive closes that connection (no answer to a ping: 10s without a
// read, then 2s) and fails; a re-dial's handshake never completes (grpc waits for the server's
// preface), so grpc's round-robin balancer picks only the other two members' connections from then
// on. A client pings only while it has calls in flight (PermitWithoutStream false, as etcd's
// server requires: its policy refuses pings on an idle connection), so each client finds its dead
// connection when it first sends a call on it: at most three keepalive closes, one per client,
// each holding the workers that picked it for up to 12s. The phase ends once some operation has
// failed, 13s have passed, none has failed for 2s, and every client has served an operation since
// the last failure.
//
// Return: member 1's bridge is unblackholed (which closes its connections: the clients' stalled
// re-dials end, and the next one completes), and 3s later members 2 and 3's bridges are
// blackholed and their connections dropped (their calls in flight fail at once; their re-dials
// never complete). From then on only member 1 can answer.
//
// It checks porcupine's verdict is Ok; every failure in the first phase at a keepalive close (at
// least 10s in); every client served an operation started after the last failure and ended before
// the unblackhole (failover); and every client served an operation started after members 2 and 3
// were cut (its return to member 1). 3 workers of 12000 operations, each after a 2ms pause, so the
// run outlasts both phases. It runs in a child process (inChild), as TestMainRun.
func TestFailover(t *testing.T) {
	if inChild(t, "TestFailover") {
		return
	}
	srvs, brs, clis := cutSetup(t, func(int) []string { return bridgeAddrs })
	var cmu sync.Mutex
	var unblackholeAt, cutAt time.Duration
	control := func(snap func() []cutOp, since func() time.Duration) {
		time.Sleep(50 * time.Millisecond)
		brs[0].Blackhole()
		for {
			time.Sleep(200 * time.Millisecond)
			ops, now := snap(), since()
			var lastFail time.Duration
			failed := false
			for _, op := range ops {
				if op.err {
					failed = true
					if op.end > lastFail {
						lastFail = op.end
					}
				}
			}
			if !failed || now < 13*time.Second || now-lastFail < 2*time.Second {
				continue
			}
			var served [3]bool
			for _, op := range ops {
				if !op.err && op.start > lastFail {
					served[op.cli] = true
				}
			}
			if served[0] && served[1] && served[2] {
				break
			}
		}
		cmu.Lock()
		unblackholeAt = since()
		cmu.Unlock()
		brs[0].Unblackhole()
		time.Sleep(3 * time.Second)
		brs[1].Blackhole()
		brs[2].Blackhole()
		brs[1].DropConnections()
		brs[2].DropConnections()
		cmu.Lock()
		cutAt = since()
		cmu.Unlock()
	}
	ops := cutRun(t, srvs, brs, clis, nil, 12000, 2*time.Millisecond, control)
	cmu.Lock()
	ub, ct := unblackholeAt, cutAt
	cmu.Unlock()
	if ct == 0 {
		t.Fatalf("the run ended before members 2 and 3 were cut")
	}
	t.Logf("member 1 unblackholed at %v, members 2 and 3 cut at %v", ub, ct)
	var lastFail time.Duration
	failed := false
	for _, op := range ops {
		if op.err && op.end < ub {
			t.Logf("failed: client %d, %v to %v", op.cli+1, op.start, op.end)
			if op.end < 10*time.Second {
				t.Fatalf("an operation failed at %v, before keepalive could close a connection", op.end)
			}
			failed = true
			if op.end > lastFail {
				lastFail = op.end
			}
		}
	}
	if !failed {
		t.Fatalf("no operation failed: the blackhole cut nothing")
	}
	var okAfter, okBack [3]int
	for _, op := range ops {
		if !op.err && op.start > lastFail && op.end < ub {
			okAfter[op.cli]++
		}
		if !op.err && op.start > ct {
			okBack[op.cli]++
		}
	}
	t.Logf("operations succeeded after the last failure (%v), during the cut, per client: %v",
		lastFail, okAfter)
	t.Logf("operations succeeded with only member 1 reachable, per client: %v", okBack)
	for i := range clis {
		if okAfter[i] == 0 {
			t.Fatalf("no operation through client %d succeeded during the cut: no failover", i+1)
		}
		if okBack[i] == 0 {
			t.Fatalf("no operation through client %d succeeded with only member 1 reachable: "+
				"no return to member 1", i+1)
		}
	}
}
