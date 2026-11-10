package crashreconf

// The real run of the program (notes/specs-only/crashreconf-test.md): each member node a process
// of its own (this test binary re-executed with CRASHRECONF_SLOT set, in the slot's directory,
// running RunMember), the client node in the test's process, and a crasher that kills member
// processes with SIGKILL at random times and starts them again on the same directory. Not
// translated.
//
//	go test ./etcd/crashreconf/                                  # one short round
//	go test ./etcd/crashreconf/ -crashreconf.soak=10m -timeout=0 # rounds for ten minutes
//
// The client node's body is RunClient's (Connect, WaitCluster, Reconfigure, the workload, the
// check), with the workload driven here as lintest.Run drives it (runWorkload) so that the history
// is kept: on Illegal it is written, with porcupine's visualization and the nodes' logs, to a
// directory the test names.

import (
	"bytes"
	"encoding/json"
	"flag"
	"fmt"
	"math/rand"
	"os"
	"os/exec"
	"path/filepath"
	"strconv"
	"sync"
	"sync/atomic"
	"syscall"
	"testing"
	"time"

	"github.com/anishathalye/porcupine"
	"go.uber.org/zap"
	"go.uber.org/zap/zapcore"
	"go.uber.org/zap/zaptest/observer"

	"github.com/mit-pdos/etcd-grove/examples/etcd/txnlin"
	"github.com/mit-pdos/etcd-grove/examples/lib/lintest"
)

var (
	flagSoak    = flag.Duration("crashreconf.soak", 0, "run rounds until this much time is spent (0: one round)")
	flagClients = flag.Int("crashreconf.clients", 3, "concurrent workload clients")
	flagOps     = flag.Int("crashreconf.ops", 150, "operations per client")
	flagPace    = flag.Duration("crashreconf.pace", 100*time.Millisecond, "each client's pause before an operation")
	flagSeed    = flag.Int64("crashreconf.seed", 0, "the crasher's seed (0: the clock)")
	flagKillMin = flag.Duration("crashreconf.killmin", 2*time.Second, "least time between two kills")
	flagKillMax = flag.Duration("crashreconf.killmax", 6*time.Second, "most time between two kills")
	flagCheck   = flag.Duration("crashreconf.checktimeout", 3*time.Minute, "porcupine's timeout")
	flagKeep    = flag.Bool("crashreconf.keep", false, "keep every round's directory")
)

const slotEnv = "CRASHRECONF_SLOT"

func TestMain(m *testing.M) {
	if s := os.Getenv(slotEnv); s != "" {
		i, err := strconv.Atoi(s)
		if err != nil {
			fmt.Fprintln(os.Stderr, "bad", slotEnv, s)
			os.Exit(2)
		}
		RunMember(i, nodeLogger())
		os.Exit(3) // RunMember never returns
	}
	os.Exit(m.Run())
}

// nodeLogger logs at Info to node.log in the node's directory.
func nodeLogger() *zap.Logger {
	cfg := zap.NewProductionConfig()
	cfg.Encoding = "console"
	cfg.EncoderConfig = zap.NewDevelopmentEncoderConfig()
	cfg.OutputPaths = []string{"node.log"}
	cfg.ErrorOutputPaths = []string{"node.log"}
	cfg.Sampling = nil
	lg, err := cfg.Build()
	if err != nil {
		panic(err)
	}
	return lg
}

// A node: a member slot's process, started again after every kill.
type node struct {
	slot int
	dir  string

	mu         sync.Mutex
	cmd        *exec.Cmd
	exited     chan struct{}
	killing    bool
	unexpected []string // exits we did not cause
	starts     int
}

func (n *node) start() error {
	n.mu.Lock()
	defer n.mu.Unlock()
	out, err := os.OpenFile(filepath.Join(n.dir, "out.log"), os.O_APPEND|os.O_CREATE|os.O_WRONLY, 0o644)
	if err != nil {
		return err
	}
	cmd := exec.Command(os.Args[0], "-test.run=^$")
	cmd.Env = append(os.Environ(), slotEnv+"="+strconv.Itoa(n.slot))
	cmd.Dir = n.dir
	cmd.Stdout = out
	cmd.Stderr = out
	cmd.SysProcAttr = &syscall.SysProcAttr{Pdeathsig: syscall.SIGKILL}
	if err := cmd.Start(); err != nil {
		out.Close()
		return err
	}
	n.starts++
	exited := make(chan struct{})
	n.cmd, n.exited, n.killing = cmd, exited, false
	go func() {
		err := cmd.Wait()
		out.Close()
		n.mu.Lock()
		if !n.killing {
			n.unexpected = append(n.unexpected, fmt.Sprintf("slot %d exited by itself: %v", n.slot, err))
		}
		n.mu.Unlock()
		close(exited)
	}()
	return nil
}

// kill kills the node's process (SIGKILL) and waits for it to exit.
func (n *node) kill() {
	n.mu.Lock()
	cmd, exited := n.cmd, n.exited
	n.killing = true
	n.mu.Unlock()
	if cmd == nil {
		return
	}
	cmd.Process.Kill()
	<-exited
}

// crasher kills a node picked at random every killmin to killmax, and starts it again after 100 to
// 800ms, until stop is closed; at most one node is down at a time. It counts the kills.
func crasher(rng *rand.Rand, nodes []*node, stop chan struct{}, kills *atomic.Int64, errs chan error) {
	span := int64(*flagKillMax - *flagKillMin)
	for {
		d := *flagKillMin + time.Duration(rng.Int63n(span+1))
		select {
		case <-stop:
			return
		case <-time.After(d):
		}
		n := nodes[rng.Intn(len(nodes))]
		n.kill()
		kills.Add(1)
		time.Sleep(time.Duration(100+rng.Intn(700)) * time.Millisecond)
		if err := n.start(); err != nil {
			errs <- err
			return
		}
	}
}

// runWorkload is lintest.Run's driver (runClient on clients goroutines, ops operations each,
// txnlin.Gen's inputs, the monotonic clock), with a pause of pace before each operation; it
// returns the history.
func runWorkload(apply func(any) any, clients int, ops int, pace time.Duration) []porcupine.Operation {
	clock := lintest.MonotonicClock()
	hs := make([][]porcupine.Operation, clients)
	var wg sync.WaitGroup
	for id := 0; id < clients; id++ {
		wg.Add(1)
		go func() {
			defer wg.Done()
			for i := 0; i < ops; i++ {
				time.Sleep(pace)
				in := txnlin.Gen(id)
				call := clock()
				out := apply(in)
				ret := clock()
				hs[id] = append(hs[id], porcupine.Operation{ClientId: id, Input: in, Call: call, Output: out, Return: ret})
			}
		}()
	}
	wg.Wait()
	var all []porcupine.Operation
	for _, h := range hs {
		all = append(all, h...)
	}
	return all
}

// A round's result.
type round struct {
	seed                                    int64
	dir                                     string
	result                                  porcupine.CheckResult
	ops, failed                             int
	kills                                   int64
	adds, promotes, removes, learnerRemoves int
	joins, retired                          int
	logCounts                               map[string]int
	workload, check                         time.Duration
	unexpected                              []string
}

func (r round) String() string {
	return fmt.Sprintf("seed %d: %v; %d ops (%d failed) in %v, check %v; %d kills; %d adds, %d promotions, "+
		"%d voter removals, %d learner removals; %d members joined, %d retired; nodes: %v", r.seed,
		r.result, r.ops, r.failed, r.workload.Round(time.Millisecond), r.check.Round(time.Millisecond),
		r.kills, r.adds, r.promotes, r.removes, r.learnerRemoves, r.joins, r.retired, r.logCounts)
}

// What runRound counts in the nodes' logs.
var logMarks = map[string]string{
	"started":        MsgStarted,
	"startFailed":    MsgStartFailed,
	"listenFailed":   MsgListenFailed,
	"stopped":        MsgStopped,
	"elections":      "elected leader",
	"snapApplied":    "applying snapshot",
	"snapSent":       "sent database snapshot",
	"removedStopped": "data-dir used by this member must be removed",
	"selfRemoved":    "the member has been permanently removed",
	// a handler's panic, recovered by net/http (rafthttp's pipeline handler panics on every
	// Process error: a message to a member's previous incarnation at its reused peer URL)
	"handlerPanics": "http: panic serving",
}

// runRound runs the program once in a fresh directory under base: the member nodes, the crasher,
// the client node's body. It keeps the directory if the result is not Ok (or -crashreconf.keep).
func runRound(t *testing.T, base string, seed int64) round {
	dir, err := os.MkdirTemp(base, "round-")
	if err != nil {
		t.Fatal(err)
	}
	r := round{seed: seed, dir: dir}
	rng := rand.New(rand.NewSource(seed))

	var nodes []*node
	for i := 0; i < NSlots; i++ {
		nd := filepath.Join(dir, "slot"+strconv.Itoa(i))
		if err := os.Mkdir(nd, 0o755); err != nil {
			t.Fatal(err)
		}
		n := &node{slot: i, dir: nd}
		if err := n.start(); err != nil {
			t.Fatal(err)
		}
		nodes = append(nodes, n)
	}
	defer func() {
		for _, n := range nodes {
			n.kill()
		}
	}()

	// the client node (RunClient's body)
	core, logs := observer.New(zapcore.InfoLevel)
	lg := zap.New(core)
	kvs, admin, ok := Connect()
	if !ok {
		t.Fatal("clientv3.New failed")
	}
	defer func() {
		for _, c := range append(kvs, admin) {
			c.Close()
		}
	}()
	waited := make(chan struct{})
	go func() { WaitCluster(admin); close(waited) }()
	select {
	case <-waited:
	case <-time.After(60 * time.Second):
		t.Fatal("the cluster did not answer a member list in 60s")
	}

	stop := make(chan struct{})
	var kills atomic.Int64
	cerrs := make(chan error, 1)
	var cwg sync.WaitGroup
	cwg.Add(1)
	go func() { defer cwg.Done(); crasher(rng, nodes, stop, &kills, cerrs) }()

	done := new(atomic.Bool)
	var rwg sync.WaitGroup
	rwg.Add(1)
	go func() { defer rwg.Done(); Reconfigure(admin, kvs, done, lg) }()

	start := time.Now()
	apply := func(input any) any { return Apply(kvs, input) }
	hist := runWorkload(apply, *flagClients, *flagOps, *flagPace)
	r.workload = time.Since(start)
	done.Store(true)
	close(stop)
	cwg.Wait()
	rwg.Wait()
	select {
	case err := <-cerrs:
		t.Fatalf("crasher: %v", err)
	default:
	}
	for _, n := range nodes {
		n.kill()
	}

	r.kills = kills.Load()
	r.adds = logs.FilterMessage(MsgAdded).Len()
	r.promotes = logs.FilterMessage(MsgPromoted).Len()
	r.removes = logs.FilterMessage(MsgRemoved).Len()
	r.learnerRemoves = logs.FilterMessage(MsgLearnerRemoved).Len()
	r.ops = len(hist)
	for _, op := range hist {
		if op.Output.(txnlin.Output).Err {
			r.failed++
		}
	}
	for _, n := range nodes {
		r.unexpected = append(r.unexpected, n.unexpected...)
	}
	// the incarnations: every data directory but the initial members', and the removal markers
	for _, n := range nodes {
		dirs, _ := filepath.Glob(filepath.Join(n.dir, "s*-*.etcd"))
		marks, _ := filepath.Glob(filepath.Join(n.dir, "s*-*.removed"))
		r.joins += len(dirs)
		r.retired += len(marks)
		if n.slot < NInitial && len(dirs) > 0 {
			r.joins--
		}
	}
	r.logCounts = map[string]int{}
	for _, n := range nodes {
		for _, f := range []string{"node.log", "out.log"} {
			b, _ := os.ReadFile(filepath.Join(n.dir, f))
			for k, m := range logMarks {
				r.logCounts[k] += bytes.Count(b, []byte(m))
			}
		}
	}

	cstart := time.Now()
	model := txnlin.Model()
	res, info := porcupine.CheckOperationsVerbose(model, hist, *flagCheck)
	r.check = time.Since(cstart)
	r.result = res
	if res != porcupine.Ok || len(r.unexpected) > 0 || *flagKeep {
		// keep the round: the history, porcupine's visualization and the nodes' directories
		if b, err := json.Marshal(hist); err == nil {
			os.WriteFile(filepath.Join(dir, "history.json"), b, 0o644)
		}
		if res == porcupine.Illegal {
			porcupine.VisualizePath(model, info, filepath.Join(dir, "porcupine.html"))
		}
		t.Logf("kept %s", dir)
	} else {
		os.RemoveAll(dir)
	}
	return r
}

// TestCrashReconf runs the program for real: one round (-crashreconf.soak: rounds until the
// duration is spent). It fails on Illegal (a real finding: the round's directory is kept, with the
// history and porcupine's visualization), on a node that exited by itself (a panic, a fatal error:
// its out.log), on a round without kills or without a membership change, and on Unknown
// (porcupine's timeout).
func TestCrashReconf(t *testing.T) {
	// the rounds' directories, outside go test's temporary directory so that a kept round outlives
	// the test; removed at the end if no round was kept
	base, err := os.MkdirTemp("", "crashreconf-")
	if err != nil {
		t.Fatal(err)
	}
	defer os.Remove(base)
	seed := *flagSeed
	if seed == 0 {
		seed = time.Now().UnixNano()
	}
	deadline := time.Now().Add(*flagSoak)
	counts := map[porcupine.CheckResult]int{}
	var tot round
	for n := 0; ; n++ {
		r := runRound(t, base, seed+int64(n))
		t.Logf("round %d: %v", n, r)
		counts[r.result]++
		tot.ops += r.ops
		tot.failed += r.failed
		tot.kills += r.kills
		tot.adds += r.adds
		tot.promotes += r.promotes
		tot.removes += r.removes
		tot.learnerRemoves += r.learnerRemoves
		if r.result == porcupine.Illegal {
			t.Errorf("round %d: ILLEGAL: porcupine found the history not linearizable (seed %d, kept in %s)",
				n, r.seed, r.dir)
		}
		if len(r.unexpected) > 0 {
			t.Errorf("round %d: %v (kept in %s)", n, r.unexpected, r.dir)
		}
		if *flagSoak == 0 {
			if r.result == porcupine.Unknown {
				t.Errorf("porcupine timed out (%v)", *flagCheck)
			}
			if r.kills == 0 {
				t.Errorf("no member was killed")
			}
			if r.adds+r.removes == 0 {
				t.Errorf("no membership change")
			}
		}
		if t.Failed() || !time.Now().Before(deadline) {
			break
		}
	}
	t.Logf("%d rounds: %d Ok, %d Unknown, %d Illegal; %d ops (%d failed), %d kills, %d adds, "+
		"%d promotions, %d voter removals, %d learner removals",
		counts[porcupine.Ok]+counts[porcupine.Unknown]+counts[porcupine.Illegal], counts[porcupine.Ok],
		counts[porcupine.Unknown], counts[porcupine.Illegal], tot.ops, tot.failed, tot.kills, tot.adds,
		tot.promotes, tot.removes, tot.learnerRemoves)
}
