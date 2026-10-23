package linkv3p

import (
	"context"
	"fmt"
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

	"github.com/mit-pdos/etcd-grove/examples/common"
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
// once at least, its followers elect another and it steps down: CheckQuorum; a write at an
// isolated member fails after the request timeout, 7s, a read is retried at the next member, and
// some member is isolated until the
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
	read       bool // a Get or a List: a Range, which the client retries
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
		cli, err := common.NewClients(eps(i), lg)
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
		kind := input.(linkvtxn.Input).Kind
		mu.Lock()
		ops = append(ops, cutOp{i, start, end, out.(linkvtxn.Output).Err,
			kind == linkvtxn.KGet || kind == linkvtxn.KList})
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
	nReadErr := 0
	for _, op := range ops {
		if op.err {
			nErr[op.cli]++
			if op.read {
				nReadErr++
			}
		} else {
			nOk[op.cli]++
		}
	}
	nTimedOut := 0
	for _, op := range ops {
		if timedOut(op) {
			nTimedOut++
		}
	}
	t.Logf("operations per client: succeeded %v, failed %v (%d of the failures reads, %d of them "+
		"request timeouts)", nOk, nErr, nReadErr, nTimedOut)
	if nOk[0]+nOk[1]+nOk[2] == 0 {
		t.Fatalf("every operation failed")
	}
	// every member stays reachable through some client's bridge or comes back (a read held by a
	// cut is retried after it, on the next member: notes/read-retry-plan.md), unless the read's
	// request timeout fires first: the client never retries past the caller's deadline
	// (notes/client-timeouts-plan.md)
	nReadErrFast := 0
	for _, op := range ops {
		if op.err && op.read && !timedOut(op) {
			nReadErrFast++
		}
	}
	if nReadErrFast > 0 {
		t.Fatalf("%d reads failed before their request timeout: the client's retries did not cover "+
			"them", nReadErrFast)
	}
	return ops
}

// timedOut: the operation op failed at its request timeout (common.RequestTimeout after its
// start, give or take: linkvtxn.Apply reports only that a call failed).
func timedOut(op cutOp) bool {
	d := op.end - op.start
	return op.err && d > common.RequestTimeout-500*time.Millisecond &&
		d < common.RequestTimeout+2*time.Second
}

// The bridges' addresses, by member.
var bridgeAddrs = []string{bridgeAddr1, bridgeAddr2, bridgeAddr3}

// TestClientCuts shows the clients' cuts and recovery at the same member (notes/client-cut-plan.md,
// D-C5): each client of one member's bridge, on a schedule that drops member 2's client
// connections at 20ms and 50ms and blackholes member 1's client from 0.1s to 3.1s. It checks:
// porcupine's verdict is Ok; some operation through client 1 was cut (a call in flight during the
// blackhole hangs, and the unblackhole closes its connection: Unavailable, which fails a write and
// has a read retried, so the read is held over the blackhole; the clients are connected first,
// warmed up); some operation through client 1 that started after the unblackhole succeeded (gRPC
// re-dialed the bridge); no read failed (cutRun); and the history is not all errors.
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
	var cut1, okAfter1 bool
	for _, op := range ops {
		// cut: a write failed, or a read held by the blackhole (retried once it ended)
		if op.cli == 0 && (op.err || (op.start < unblackholeAt && op.end > unblackholeAt &&
			op.end-op.start > time.Second)) {
			cut1 = true
		}
		if op.cli == 0 && !op.err && op.start > unblackholeAt {
			okAfter1 = true
		}
	}
	if !cut1 {
		t.Fatalf("no operation through client 1 failed or was held: the blackhole cut nothing")
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
// hangs until its request timeout (common.RequestTimeout, 5s) and fails, write or read (the client
// never retries past the caller's deadline: notes/client-timeouts-plan.md); the balancer keeps
// picking that connection for a third of the calls until the client's keepalive closes it (no
// answer to a ping: 10s without a read, grpc's floor over common.KeepAliveTime, then
// common.KeepAliveTimeout, 6s); a re-dial's handshake never completes (grpc waits for the server's
// preface), so grpc's round-robin balancer picks only the other two members' connections from then
// on. A client pings only while it has calls in flight (PermitWithoutStream false, as etcd's
// server requires: its policy refuses pings on an idle connection), so each client finds its dead
// connection when it first sends a call on it: at most three keepalive closes, one per client,
// each preceded by request timeouts for up to 16s. The phase ends once some operation has
// stalled, 20s have passed, none has stalled for 2s, and every client has served an operation
// since the last stall.
//
// Return: member 1's bridge is unblackholed (which closes its connections: the clients' stalled
// re-dials end, and the next one completes), and 3s later members 2 and 3's bridges are
// blackholed and their connections dropped (their writes in flight fail at once, their reads are
// retried; their re-dials never complete). From then on only member 1 can answer.
//
// It checks porcupine's verdict is Ok; every stall in the first phase ended by a request timeout
// or later (none before 5s), some of them request timeouts, the last one after the keepalive's
// first ping (10s: the stalls go on until the close); every client served an operation started
// after the last stall and ended before the unblackhole (failover); every client served an
// operation started after members 2 and 3 were cut (its return to member 1); and no read failed
// before its request timeout (cutRun). 3 workers of 12000 operations, each after a 2ms pause, so
// the run outlasts both phases. It runs in a child process (inChild), as TestMainRun.
func TestFailover(t *testing.T) {
	// an operation the blackhole stalled: one that failed (at its request timeout, or at the
	// keepalive close), or a read held longer than a request timeout; the run's other operations
	// take milliseconds
	stalled := func(op cutOp) bool { return op.err || op.end-op.start > common.RequestTimeout }
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
				if stalled(op) {
					failed = true
					if op.end > lastFail {
						lastFail = op.end
					}
				}
			}
			if !failed || now < 20*time.Second || now-lastFail < 2*time.Second {
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
	failed, nTimedOut := false, 0
	for _, op := range ops {
		if stalled(op) && op.end < ub {
			t.Logf("stalled: client %d, %v to %v (read %v, failed %v, timed out %v)", op.cli+1,
				op.start, op.end, op.read, op.err, timedOut(op))
			if op.end < common.RequestTimeout {
				t.Fatalf("an operation stalled until %v, before a request timeout could fire", op.end)
			}
			if timedOut(op) {
				nTimedOut++
			}
			failed = true
			if op.end > lastFail {
				lastFail = op.end
			}
		}
	}
	if !failed {
		t.Fatalf("no operation stalled: the blackhole cut nothing")
	}
	if nTimedOut == 0 {
		t.Fatalf("no operation failed at its request timeout")
	}
	if lastFail < 10*time.Second {
		t.Fatalf("the last stall ended at %v, before keepalive's first ping: the dead connection "+
			"was given up early", lastFail)
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
	t.Logf("operations succeeded after the last stall (%v), during the cut, per client: %v",
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

// TestWriteOnce checks that the client's retries never send a write twice
// (notes/read-retry-plan.md, R0): the clients have the default retries, which retry a write only
// after a refusal (a learner's, an authentication error), which these members never send. 3
// workers each put distinct keys through Main's clients (every client of all three bridges) for
// 20s, while member 1's bridge is blackholed from 50ms to 15s (a write in flight fails at its
// request timeout) and member 2's client connections are dropped every second (a write in flight
// on them fails at once). Then each key must have been put at most once: its version, the number of puts
// since its creation, is 1. It runs in a child process (inChild), as TestMainRun.
func TestWriteOnce(t *testing.T) {
	if inChild(t, "TestWriteOnce") {
		return
	}
	_, brs, clis := cutSetup(t, func(int) []string { return bridgeAddrs })
	go func() {
		time.Sleep(50 * time.Millisecond)
		brs[0].Blackhole()
		for i := 0; i < 14; i++ {
			time.Sleep(time.Second)
			brs[1].DropConnections()
		}
		time.Sleep(time.Second)
		brs[0].Unblackhole()
	}()
	var wg sync.WaitGroup
	var mu sync.Mutex
	var keys []string
	nErr := 0
	deadline := time.Now().Add(20 * time.Second)
	for w := 0; w < 3; w++ {
		wg.Add(1)
		go func(w int) {
			defer wg.Done()
			for i := 0; time.Now().Before(deadline); i++ {
				key := fmt.Sprintf("once/%d/%d", w, i)
				_, err := clis[rand.Intn(len(clis))].Put(context.Background(), key, "v")
				mu.Lock()
				keys = append(keys, key)
				if err != nil {
					nErr++
				}
				mu.Unlock()
			}
		}(w)
	}
	wg.Wait()
	t.Logf("%d puts, %d failed", len(keys), nErr)
	if nErr == 0 {
		t.Fatalf("no put failed: the cuts cut nothing")
	}
	ctx, cancel := context.WithTimeout(context.Background(), 30*time.Second)
	defer cancel()
	resp, err := clis[0].Get(ctx, "once/", clientv3.WithPrefix())
	if err != nil {
		t.Fatal(err)
	}
	for _, kv := range resp.Kvs {
		if kv.Version != 1 {
			t.Fatalf("key %s put %d times", kv.Key, kv.Version)
		}
	}
	t.Logf("%d keys, each put once", len(resp.Kvs))
}

// A watched event of TestWatchFailover: its revision, key, value, whether it is a put, and when it
// arrived (since the run's start).
type wEvent struct {
	rev      int64
	key, val string
	put      bool
	at       time.Duration
}

// A put of TestWatchFailover's writers: its key and value, and for one that returned no error its
// reply's revision.
type wPut struct {
	key, val string
	rev      int64
	ok       bool
}

// checkEvents fails the test unless the events evs are the writes puts, as watchkv's check: all
// puts, at revisions 2, 3, ... without a gap or a repeat (a fresh cluster is at revision 1, and
// every write is a put of one key), each a put some writer attempted, and every put that returned
// no error the event at its reply's revision with its key and value.
func checkEvents(t *testing.T, evs []wEvent, puts []wPut) {
	t.Helper()
	tried := map[[2]string]bool{}
	for _, p := range puts {
		tried[[2]string{p.key, p.val}] = true
	}
	for i, e := range evs {
		if !e.put {
			t.Fatalf("event %d at revision %d is not a put", i, e.rev)
		}
		if e.rev != int64(i)+2 {
			t.Fatalf("event %d at revision %d, expected %d: a gap or a repeat (the previous at %d)",
				i, e.rev, i+2, evs[max(i-1, 0)].rev)
		}
		if !tried[[2]string{e.key, e.val}] {
			t.Fatalf("event at revision %d puts %s=%s, which no writer attempted", e.rev, e.key,
				e.val)
		}
	}
	for _, p := range puts {
		if !p.ok {
			continue
		}
		i := p.rev - 2
		if i < 0 || i >= int64(len(evs)) {
			t.Fatalf("the put of %s=%s at revision %d was not watched", p.key, p.val, p.rev)
		}
		if e := evs[i]; e.key != p.key || e.val != p.val {
			t.Fatalf("the event at revision %d is %s=%s, the put there %s=%s", p.rev, e.key, e.val,
				p.key, p.val)
		}
	}
}

// TestWatchFailover shows a watch surviving the cut of the member it streams from
// (notes/watch-cut-plan.md, W0): every client of all three bridges, as Main's; a prefix watch from
// revision 1 through client 1, opened before any write; 3 writers putting keys under the prefix
// (watchkv's workload: a few keys and values) through clients picked at random, each put after a
// 2ms pause; and the bridges blackholed in turn, each for 18s, then unblackholed: whichever member
// the watch streams from is cut once at least. A cut stream's connection is closed by the client's
// keepalive (the stream is a call in flight, so the client pings: 10s, grpc's floor, then
// common.KeepAliveTimeout, 6s; the puts on it fail at their request timeout meanwhile), and the
// watch client re-opens the stream on the same client, which grpc's balancer sends to a reachable member,
// resuming each watch from the revision after the last event it delivered.
//
// After the writers stop, the watch is read up to the highest revision a put returned (30s at
// most). It checks: the events are the writes (checkWatch: no gap, no repeat, every successful put
// its event); the events stalled (no event for 10s while puts succeeded: a cut of the stream's
// member) and resumed; and some put succeeded during each blackhole. It runs in a child process
// (inChild), as TestMainRun.
func TestWatchFailover(t *testing.T) {
	if inChild(t, "TestWatchFailover") {
		return
	}
	_, brs, clis := cutSetup(t, func(int) []string { return bridgeAddrs })
	t0 := time.Now()
	wctx, cancel := context.WithCancel(context.Background())
	defer cancel()
	wch := clis[0].Watch(wctx, "wk/", clientv3.WithPrefix(), clientv3.WithRev(1),
		clientv3.WithCreatedNotify(), clientv3.WithProgressNotify())

	var mu sync.Mutex
	var evs []wEvent
	var werr error
	watchDone := make(chan struct{})
	go func() {
		defer close(watchDone)
		for wresp := range wch {
			if err := wresp.Err(); err != nil {
				mu.Lock()
				werr = err
				mu.Unlock()
				return
			}
			at := time.Since(t0)
			mu.Lock()
			for _, e := range wresp.Events {
				evs = append(evs, wEvent{e.Kv.ModRevision, string(e.Kv.Key), string(e.Kv.Value),
					e.Type == clientv3.EventTypePut, at})
			}
			mu.Unlock()
		}
	}()

	// the blackholes, in turn; the writers run until the last one ends, and 3s more
	const hole = 18 * time.Second
	var holes [3][2]time.Duration
	stop := make(chan struct{})
	go func() {
		for i := range brs {
			time.Sleep(time.Second)
			holes[i][0] = time.Since(t0)
			brs[i].Blackhole()
			time.Sleep(hole)
			brs[i].Unblackhole()
			holes[i][1] = time.Since(t0)
		}
		time.Sleep(3 * time.Second)
		close(stop)
	}()

	keys := []string{"wk/k0", "wk/k1", "wk/k2"}
	vals := []string{"a", "b", "c", "d"}
	var puts []wPut
	var putAt []time.Duration // when each successful put returned
	var wg sync.WaitGroup
	for w := 0; w < 3; w++ {
		wg.Add(1)
		go func() {
			defer wg.Done()
			for {
				select {
				case <-stop:
					return
				default:
				}
				time.Sleep(2 * time.Millisecond)
				mu.Lock()
				p := wPut{key: keys[rand.Intn(len(keys))], val: vals[rand.Intn(len(vals))]}
				cli := clis[rand.Intn(len(clis))]
				mu.Unlock()
				resp, err := cli.Put(context.Background(), p.key, p.val)
				if err == nil {
					p.rev, p.ok = resp.Header.Revision, true
				}
				mu.Lock()
				puts = append(puts, p)
				if err == nil {
					putAt = append(putAt, time.Since(t0))
				}
				mu.Unlock()
			}
		}()
	}
	wg.Wait()

	var maxRev int64
	nOk := 0
	mu.Lock()
	for _, p := range puts {
		if p.ok {
			nOk++
			maxRev = max(maxRev, p.rev)
		}
	}
	mu.Unlock()
	t.Logf("%d puts, %d succeeded, the highest revision %d; blackholes %v", len(puts), nOk, maxRev,
		holes)
	deadline := time.Now().Add(30 * time.Second)
	for {
		mu.Lock()
		n, err := len(evs), werr
		var last int64
		if n > 0 {
			last = evs[n-1].rev
		}
		mu.Unlock()
		if last >= maxRev {
			break
		}
		if err != nil {
			t.Fatalf("the watch ended at revision %d: %v", last, err)
		}
		if time.Now().After(deadline) {
			t.Fatalf("the watch reached revision %d only, of %d", last, maxRev)
		}
		time.Sleep(100 * time.Millisecond)
	}
	cancel()
	<-watchDone
	mu.Lock()
	defer mu.Unlock()
	checkEvents(t, evs, puts)
	t.Logf("%d events, revisions 2 to %d, no gap or repeat", len(evs), evs[len(evs)-1].rev)

	// the stalls: no event for 5s or more (the run's puts succeed every few milliseconds)
	stalled := false
	prev := time.Duration(0)
	for i, e := range evs {
		if e.at-prev > 5*time.Second {
			t.Logf("no event from %v to %v (revision %d next)", prev, e.at, e.rev)
			if e.at-prev >= 10*time.Second && i > 0 {
				stalled = true
			}
		}
		prev = e.at
	}
	if !stalled {
		t.Fatalf("the events never stalled: no blackhole cut the watch's stream")
	}
	for i, h := range holes {
		ok := false
		for _, at := range putAt {
			if at > h[0] && at < h[1] {
				ok = true
				break
			}
		}
		if !ok {
			t.Fatalf("no put succeeded during member %d's blackhole: no failover for writes", i+1)
		}
	}
}

// TestMainWatch runs MainWatch for real (notes/watch-cut-plan.md, W4): three members in a fresh
// directory, 3 writers of 300 puts each, on TestMainRun's schedule (each member isolated in turn
// for three seconds, member 3's client blackholed during the first isolation, member 2's client
// connections dropped as it ends). The check must pass. Then it asks each member, which MainWatch
// left running, for the prefix's revision (so that the check was not vacuous). It runs in a child
// process (inChild), as TestMainRun.
func TestMainWatch(t *testing.T) {
	if inChild(t, "TestMainWatch") {
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
	if r := MainWatch(3, 300, sched); r != WatchOk {
		t.Fatalf("got %v", r)
	}
	t.Logf("MainWatch took %v", time.Since(start))
	for i, addr := range []string{clientAddr1, clientAddr2, clientAddr3} {
		cli, err := clientv3.New(clientv3.Config{Endpoints: []string{addr}, Logger: zap.NewNop()})
		if err != nil {
			t.Fatal(err)
		}
		ctx, cancel := context.WithTimeout(context.Background(), 10*time.Second)
		resp, err := cli.Get(ctx, wprefix, clientv3.WithPrefix())
		cancel()
		cli.Close()
		if err != nil {
			t.Fatalf("member %d: %v", i+1, err)
		}
		if resp.Header.Revision < 100 {
			t.Fatalf("member %d: the puts did not take effect: revision %d", i+1,
				resp.Header.Revision)
		}
		t.Logf("member %d: revision %d, keys %d", i+1, resp.Header.Revision, len(resp.Kvs))
	}
}
