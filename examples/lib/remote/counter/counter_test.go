package counter

import (
	"io"
	"math/rand"
	"net"
	"os"
	"os/exec"
	"path/filepath"
	"sync/atomic"
	"testing"
	"time"

	"github.com/anishathalye/porcupine"
	"github.com/mit-pdos/etcd-grove/examples/lib/lintest"
	lcounter "github.com/mit-pdos/etcd-grove/examples/lib/lintest/counter"
	"github.com/mit-pdos/etcd-grove/examples/lib/lintest/perclient"
	"github.com/mit-pdos/etcd-grove/examples/lib/remote"
)

// waitListen waits until something listens at addr.
func waitListen(t *testing.T, addr string) {
	t.Helper()
	for i := 0; i < 200; i++ {
		c, err := net.Dial("tcp", addr)
		if err == nil {
			c.Close()
			return
		}
		time.Sleep(10 * time.Millisecond)
	}
	t.Fatalf("nothing listens at %s", addr)
}

// --- the model, against the configurations it stands for ---

// cfg is a configuration: the counter's value and the pending increments.
type cfg struct{ n, k int64 }

// closure is the configurations reachable from cs by pending increments taking effect.
func closure(cs map[cfg]bool) map[cfg]bool {
	out := map[cfg]bool{}
	work := []cfg{}
	for c := range cs {
		work = append(work, c)
	}
	for len(work) > 0 {
		c := work[len(work)-1]
		work = work[:len(work)-1]
		if out[c] {
			continue
		}
		out[c] = true
		if c.k > 0 {
			work = append(work, cfg{c.n + 1, c.k - 1})
		}
	}
	return out
}

// pstep is linkv's pSeq step on explicit configuration sets (PendModel.lean's PStep, between
// closures).
func pstep(cs map[cfg]bool, incr bool, o Out) map[cfg]bool {
	out := map[cfg]bool{}
	for c := range closure(cs) {
		switch {
		case o.Unknown && incr:
			out[cfg{c.n, c.k + 1}] = true
		case o.Unknown:
			out[c] = true
		case incr && o.N == c.n+1:
			out[cfg{c.n + 1, c.k}] = true
		case !incr && o.N == c.n:
			out[c] = true
		}
	}
	return closure(out)
}

// stands is the configurations a State stands for.
func stands(s State) map[cfg]bool {
	out := map[cfg]bool{}
	for j := int64(0); j <= s.K; j++ {
		out[cfg{s.Lo + j, s.K - j}] = true
	}
	return out
}

func sameSet(a, b map[cfg]bool) bool {
	if len(a) != len(b) {
		return false
	}
	for c := range a {
		if !b[c] {
			return false
		}
	}
	return true
}

// TestModelIsPending checks step against the pending-writes construction on explicit sets, on
// random operations from random states: the same verdict, and the state stands for the same set.
func TestModelIsPending(t *testing.T) {
	r := rand.New(rand.NewSource(1))
	for n := 0; n < 200000; n++ {
		s := State{Lo: int64(r.Intn(6)), K: int64(r.Intn(5))}
		incr := r.Intn(2) == 0
		o := Out{Unknown: r.Intn(4) == 0, N: int64(r.Intn(12))}
		ok, s2 := step(s, incr, o)
		want := pstep(stands(s), incr, o)
		if ok != (len(want) > 0) {
			t.Fatalf("step(%v, %v, %v) = %v, want %v", s, incr, o, ok, len(want) > 0)
		}
		if ok && !sameSet(stands(s2), want) {
			t.Fatalf("step(%v, %v, %v) = %v, stands for %v, want %v", s, incr, o, s2, stands(s2), want)
		}
	}
}

// TestModelWithoutFaults: on histories with no unknown outcome, the model agrees with
// lintest/counter's.
func TestModelWithoutFaults(t *testing.T) {
	r := rand.New(rand.NewSource(2))
	m, lm := Model(), lcounter.Model()
	for n := 0; n < 20000; n++ {
		s, ls := m.Init(), lm.Init()
		for i := 0; i < 8; i++ {
			incr := r.Intn(2) == 0
			v := int64(r.Intn(6))
			ok, s2 := m.Step(s, incr, Out{N: v})
			lok, ls2 := lm.Step(ls, incr, v)
			if ok != lok {
				t.Fatalf("verdicts differ")
			}
			if !ok {
				break
			}
			s, ls = s2, ls2
		}
	}
}

func TestCodec(t *testing.T) {
	cd := Codec()
	for _, in := range []bool{false, true} {
		v, ok := cd.DecIn(cd.EncIn(in))
		if !ok || v.(bool) != in {
			t.Fatal("input round trip")
		}
	}
	for _, o := range []Out{{}, {Unknown: true}, {N: -1}, {N: 1 << 40}} {
		v, ok := cd.DecOut(cd.EncOut(o))
		if !ok || v.(Out) != o {
			t.Fatal("output round trip")
		}
	}
	if _, ok := cd.DecIn([]byte{2}); ok {
		t.Fatal("DecIn accepted garbage")
	}
	if _, ok := cd.DecOut([]byte{2, 0, 0, 0, 0, 0, 0, 0, 0}); ok {
		t.Fatal("DecOut accepted garbage")
	}
}

// --- deployments over real sockets, in one process ---

// freePorts is three addresses nothing listens at (each deployment its own: a Serve never
// returns, so an earlier deployment's nodes keep their addresses).
func freePorts(t *testing.T) [3]string {
	var out [3]string
	var ls []net.Listener
	for i := range out {
		l, err := net.Listen("tcp", "127.0.0.1:0")
		if err != nil {
			t.Fatal(err)
		}
		ls = append(ls, l)
		out[i] = l.Addr().String()
	}
	for _, l := range ls {
		l.Close()
	}
	return out
}

// proxy forwards connections from its own address to target, injecting faults: with fault on,
// each connection is, at random, passed whole, cut after a random number of request bytes
// (before or after the request is whole), cut after a random number of reply bytes, or delayed.
type proxy struct {
	target string
	fault  bool
	cuts   atomic.Int64
	l      net.Listener
}

func startProxy(t *testing.T, target string, fault bool) *proxy {
	l, err := net.Listen("tcp", "127.0.0.1:0")
	if err != nil {
		t.Fatal(err)
	}
	p := &proxy{target: target, fault: fault, l: l}
	go func() {
		for {
			c, err := l.Accept()
			if err != nil {
				return
			}
			go p.handle(c)
		}
	}()
	return p
}

func (p *proxy) addr() string { return p.l.Addr().String() }

// copyN copies at most n bytes (all if n < 0), then closes both.
func copyN(dst, src net.Conn, n int64) {
	if n < 0 {
		io.Copy(dst, src)
	} else {
		io.CopyN(dst, src, n)
	}
	dst.Close()
	src.Close()
}

func (p *proxy) handle(c net.Conn) {
	s, err := net.Dial("tcp", p.target)
	if err != nil {
		c.Close()
		return
	}
	reqCut, repCut := int64(-1), int64(-1)
	if p.fault {
		switch rand.Intn(6) {
		case 0: // cut in the request (header or body: requests are 9 bytes)
			reqCut = int64(rand.Intn(10))
			p.cuts.Add(1)
		case 1: // cut in the reply (replies are 17 bytes)
			repCut = int64(rand.Intn(17))
			p.cuts.Add(1)
		case 2:
			time.Sleep(time.Duration(rand.Intn(300)) * time.Millisecond)
		}
	}
	go copyN(s, c, reqCut)
	copyN(c, s, repCut)
}

// deploy starts the server and two client nodes, each behind a proxy (faulty or not), and
// returns the client nodes' proxies' addresses and the server's counter.
func deploy(t *testing.T, ports [3]string, fault bool, op func(any, any) any) ([]string, *lcounter.Counter, []*proxy) {
	srv := lcounter.New()
	go remote.Serve(ports[0], srv, op, Codec(), attempt())
	waitListen(t, ports[0])
	sp := startProxy(t, ports[0], fault)
	var addrs []string
	ps := []*proxy{sp}
	for c := 0; c < 2; c++ {
		go Client(c, ports[1+c], sp.addr())
		waitListen(t, ports[1+c])
		cp := startProxy(t, ports[1+c], fault)
		ps = append(ps, cp)
		addrs = append(addrs, cp.addr())
	}
	return addrs, srv, ps
}

func serverOp(sys any, in any) any {
	return Out{N: sys.(*lcounter.Counter).Apply(in).(int64)}
}

// recordingRun is remote.Run's driver with a counting apply (the same Do), returning porcupine's
// verdict and the numbers of increments answered and of unknown outcome.
func recordingRun(addrs []string, ops int) (porcupine.CheckResult, int64, int64) {
	var answered, unknown atomic.Int64
	r := runCounting(Model(), addrs, Codec(), Gen, ops, &answered, &unknown)
	return r, answered.Load(), unknown.Load()
}

// runCounting is remote.Run's body with a counting apply (the same Do, the same driver).
func runCounting(m porcupine.Model, addrs []string, cd remote.Codec, gen func(int) any, ops int,
	answered, unknown *atomic.Int64) porcupine.CheckResult {
	apply := func(c int, in any) any {
		out := remote.Do(addrs[c], in, cd, attempt())
		if in.(bool) {
			if out.(Out).Unknown {
				unknown.Add(1)
			} else {
				answered.Add(1)
			}
		}
		return out
	}
	return perclient.Run(m, apply, gen, lintest.CounterClock(), len(addrs), ops, 0)
}

// TestNoFaults: the deployment without faults; porcupine accepts.
func TestNoFaults(t *testing.T) {
	addrs, _, _ := deploy(t, freePorts(t), false, serverOp)
	if r := remote.Run(Model(), addrs, Codec(), Gen, 50, attempt(), 0); r != porcupine.Ok {
		t.Fatalf("porcupine: %v", r)
	}
}

// TestFaults: connections cut at random points of requests and replies, and delayed, on both
// hops, in fresh deployments (the model starts from a counter at 0); porcupine accepts every run,
// unknown-outcome increments occur, and some of them took effect (the server's counter is past
// the answered increments).
func TestFaults(t *testing.T) {
	var unknownTotal, tookEffect, cuts int64
	for run := 0; run < 10; run++ {
		addrs, srv, ps := deploy(t, freePorts(t), true, serverOp)
		r, answered, unknown := recordingRun(addrs, 30)
		if r != porcupine.Ok {
			t.Fatalf("run %d: porcupine: %v", run, r)
		}
		// wait for the server to finish what the cut connections still carry
		time.Sleep(3 * attempt())
		n := srv.Apply(false).(int64)
		if n < answered || n > answered+unknown {
			t.Fatalf("run %d: %d increments took effect, answered %d, unknown %d", run, n, answered, unknown)
		}
		unknownTotal += unknown
		tookEffect += n - answered
		for _, p := range ps {
			cuts += p.cuts.Load()
		}
	}
	t.Logf("cuts %d, unknown increments %d, of which took effect %d", cuts, unknownTotal, tookEffect)
	if unknownTotal == 0 || tookEffect == 0 {
		t.Fatalf("faults did not exercise unknown outcomes (unknown %d, took effect %d)", unknownTotal, tookEffect)
	}
}

// TestControlDoubleApply: a server that runs each increment twice is caught.
func TestControlDoubleApply(t *testing.T) {
	twice := func(sys any, in any) any {
		sys.(*lcounter.Counter).Apply(in)
		return Out{N: sys.(*lcounter.Counter).Apply(in).(int64)}
	}
	addrs, _, _ := deploy(t, freePorts(t), false, twice)
	if r := remote.Run(Model(), addrs, Codec(), Gen, 20, attempt(), 0); r != porcupine.Illegal {
		t.Fatalf("porcupine: %v, want Illegal", r)
	}
}

// --- the four commands, as processes ---

// TestProcesses builds the four commands and runs them as processes over real TCP, a fresh
// deployment each time (the model starts from a counter at 0): the orchestrator exits 0
// (porcupine accepted), and the other three are still running.
func TestProcesses(t *testing.T) {
	dir := t.TempDir()
	names := []string{"server", "client0", "client1", "orch"}
	for _, n := range names {
		cmd := exec.Command("go", "build", "-o", filepath.Join(dir, n), "./cmd/"+n)
		cmd.Stderr = os.Stderr
		if err := cmd.Run(); err != nil {
			t.Fatalf("build %s: %v", n, err)
		}
	}
	for i := 0; i < 3; i++ {
		var procs []*exec.Cmd
		exited := make([]atomic.Bool, 3)
		for j, n := range names[:3] {
			p := exec.Command(filepath.Join(dir, n))
			p.Stderr = os.Stderr
			if err := p.Start(); err != nil {
				t.Fatal(err)
			}
			procs = append(procs, p)
			go func() { p.Wait(); exited[j].Store(true) }()
		}
		for _, a := range []string{ServerAddr, ClientAddr0, ClientAddr1} {
			waitListen(t, a)
		}
		orch := exec.Command(filepath.Join(dir, "orch"))
		orch.Stderr = os.Stderr
		err := orch.Run()
		for j := range procs {
			if exited[j].Load() {
				t.Errorf("deployment %d: %s exited", i, names[j])
			}
		}
		for _, p := range procs {
			p.Process.Kill()
		}
		for j := range procs {
			for !exited[j].Load() {
				time.Sleep(10 * time.Millisecond)
			}
		}
		if err != nil {
			t.Fatalf("deployment %d: orchestrator: %v", i, err)
		}
	}
}
