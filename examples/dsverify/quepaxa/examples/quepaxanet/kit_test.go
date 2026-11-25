package quepaxanet

import (
	"bytes"
	"fmt"
	"io"
	"math/rand"
	"net"
	"os"
	"os/exec"
	"strconv"
	"strings"
	"sync/atomic"
	"testing"
	"time"

	"github.com/anishathalye/porcupine"
	"github.com/mit-pdos/etcd-grove/examples/lib/remote"
)

// The kit's deployment on loopback (the lab's kit_test.go, onto remote): every machine but the
// orchestrator is this test binary re-executed (QPNET_NODE), one process per machine: nodes 1..NC
// the client machines (clientNode), the others the server machines (serve). Node n's first address
// is all[n], its recorder address all[M+n], its configuration address all[2M+n] and a client
// machine's request address all[3M+n] (M = len(Addrs())), at free ports of 127.0.0.1. The
// orchestrator is the test, running orch with those addresses. QPNET_CHECKS=1 in a node's
// environment gives the client machines the stress test's checks (newClient(..., true)). The
// configuration is chosen at random as New chooses it, or given by QPNET_CONF
// ("N,serverMode,pipeline,epoch,timeoutUs", e.g. "5,1,5,5,40000").

func TestMain(m *testing.M) {
	if id := os.Getenv("QPNET_NODE"); id != "" {
		n, err := strconv.ParseUint(id, 10, 64)
		if err != nil {
			panic(err)
		}
		addrs, recs, cfgs, reqs := split(strings.Split(os.Getenv("QPNET_ALL"), ","))
		if n <= NC {
			clientNode(n-1, addrs, cfgs, reqs[n], os.Getenv("QPNET_CHECKS") == "1")
		}
		serve(n-NC, addrs, recs, cfgs)
		os.Exit(0)
	}
	os.Exit(m.Run())
}

// split is the loopback deployment's addresses all as the nodes' first, recorder, configuration
// and request addresses (each indexed by node).
func split(all []string) ([]string, []string, []string, []string) {
	n := len(Addrs())
	return all[:n], all[n : 2*n], all[2*n : 3*n], all[3*n:]
}

// testConf is QPNET_CONF's configuration if set, else one chosen at random.
func testConf(t *testing.T) Conf {
	e := os.Getenv("QPNET_CONF")
	if e == "" {
		return choose()
	}
	var v []byte
	for i, f := range strings.Split(e, ",") {
		x, err := strconv.ParseUint(f, 10, 64)
		if err != nil {
			t.Fatalf("QPNET_CONF %q", e)
		}
		if i == 4 {
			x /= 5000
		}
		v = append(v, byte(x))
	}
	if len(v) != confLen {
		t.Fatalf("QPNET_CONF %q is not a configuration", e)
	}
	c, ok := decode(v)
	if !ok {
		t.Fatalf("QPNET_CONF %q is not a configuration", e)
	}
	return c
}

// freeBase finds a port base b such that b+i (i < n) are free on loopback.
func freeBase(t *testing.T, n int) uint64 {
	for b := 20000 + rand.Intn(10000); b < 32000-n; b += 97 {
		ok := true
		var ls []net.Listener
		for i := 0; i < n && ok; i++ {
			l, err := net.Listen("tcp", fmt.Sprintf("127.0.0.1:%d", b+i))
			if err != nil {
				ok = false
				break
			}
			ls = append(ls, l)
		}
		for _, l := range ls {
			l.Close()
		}
		if ok {
			return uint64(b)
		}
	}
	t.Fatal("no free ports")
	return 0
}

// deploy starts the client and server machines as processes at loopback addresses and returns
// the nodes' addresses (split's four lists) and a check that no node ended.
func deploy(t *testing.T, checks bool) ([]string, []string, []string, []string, func()) {
	n := len(Addrs())
	base := freeBase(t, 4*n)
	var all []string
	for i := 0; i < 4*n; i++ {
		all = append(all, fmt.Sprintf("127.0.0.1:%d", base+uint64(i)))
	}
	type exit struct {
		id  int
		err error
		out string
	}
	exited := make(chan exit, n)
	for id := 1; id < n; id++ {
		cmd := exec.Command(os.Args[0], "-test.run=^$")
		cmd.Env = append(os.Environ(), fmt.Sprintf("QPNET_NODE=%d", id), "QPNET_ALL="+strings.Join(all, ","))
		if checks {
			cmd.Env = append(cmd.Env, "QPNET_CHECKS=1")
		} else {
			cmd.Env = append(cmd.Env, "QPNET_CHECKS=0")
		}
		var out bytes.Buffer
		cmd.Stdout = io.Discard
		cmd.Stderr = &out
		if testing.Verbose() {
			cmd.Stderr = io.MultiWriter(os.Stderr, &out)
		}
		if err := cmd.Start(); err != nil {
			t.Fatal(err)
		}
		t.Cleanup(func() { cmd.Process.Kill() })
		go func(id int) {
			err := cmd.Wait()
			exited <- exit{id, err, out.String()}
		}(id)
	}
	addrs, recs, cfgs, reqs := split(all)
	return addrs, recs, cfgs, reqs, func() {
		// The machines never return: one that ended (a panic) fails the test even when the
		// clients' history checked.
		select {
		case e := <-exited:
			t.Fatalf("node %d ended (%v):\n%s", e.id, e.err, e.out)
		default:
		}
	}
}

// TestDeployment is the orchestrator on loopback (Orch's remote.Check, through remote.Run to log
// the outcome), in the configuration testConf gives, with the stress test's checks at the client
// machines unless QPNET_CHECKS=0 (the theorem's: only the history check).
func TestDeployment(t *testing.T) {
	if testing.Short() {
		t.Skip("a deployment of 11 processes")
	}
	_, _, cfgs, reqs, check1 := deploy(t, os.Getenv("QPNET_CHECKS") != "0")
	conf := testConf(t)
	t.Logf("configuration: %s", conf)
	send(cfgs, conf)
	time.Sleep(time.Duration(StartMs) * time.Millisecond)
	var known atomic.Int64
	cdc := Codec()
	dec := cdc.DecOut
	cdc.DecOut = func(b []byte) (any, bool) {
		o, ok := dec(b)
		if ok && !o.(Out).Unknown {
			known.Add(1)
		}
		return o, ok
	}
	if r := remote.Run(Model(), reqs[1:1+NC], cdc, Gens(), int(K), attempt(), 0); r != porcupine.Ok {
		t.Fatalf("porcupine: %v", r)
	}
	t.Logf("%d of %d operations answered", known.Load(), NC*K)
	if known.Load() == 0 {
		t.Errorf("no operation was answered")
	}
	check1()
}

// TestControlPhantom (the negative control): client machines whose gets return a value nobody
// put, as a store that invents values would, are caught.
func TestControlPhantom(t *testing.T) {
	var addrs []string
	for c := uint64(0); c < NC; c++ {
		l, err := net.Listen("tcp", "127.0.0.1:0")
		if err != nil {
			t.Fatal(err)
		}
		addrs = append(addrs, l.Addr().String())
		l.Close()
	}
	phantom := func(sys any, in any) any {
		if in.(In).Put {
			return Out{}
		}
		return Out{Found: true, V: "phantom"}
	}
	for c := range addrs {
		go remote.ServeClient(c, addrs[c], func(int) any { return nil }, phantom, Codec(), attempt())
	}
	time.Sleep(200 * time.Millisecond)
	if r := remote.Run(Model(), addrs, Codec(), Gens(), int(K), attempt(), 0); r != porcupine.Illegal {
		t.Fatalf("porcupine: %v, want Illegal", r)
	}
}

// Gen's inputs have keys of KeyLen bytes ("key00000", "key00001"); a round's put and get share a
// key; put values are distinct, never empty and never NotFound.
func TestGen(t *testing.T) {
	seen := map[string]bool{}
	for c := uint64(0); c < NC; c++ {
		g := Gens()
		for j := uint64(0); j < K; j++ {
			in := Gen(c, j)
			if g(int(c)).(In) != in {
				t.Fatalf("Gens(%d) at %d", c, j)
			}
			if in.K != "key00000" && in.K != "key00001" {
				t.Errorf("Gen(%d, %d) = %+v: key", c, j, in)
			}
			if in.Put != (j%2 == 0) || (in.Put && (seen[in.V] || in.V == "" || in.V == NotFound)) {
				t.Errorf("Gen(%d, %d) = %+v", c, j, in)
			}
			seen[in.V] = true
			if j%2 == 1 && in.K != Gen(c, j-1).K {
				t.Errorf("Gen(%d, %d) = %+v: not the put's key", c, j, in)
			}
		}
	}
}

// The codec gives back every input and output; bytes that are not an encoding are refused.
func TestCodec(t *testing.T) {
	for _, in := range []In{{}, {Put: true, K: "key00000", V: "v05"}, {K: "\x00\xff", V: "x"}} {
		if x, ok := DecIn(EncIn(in)); !ok || x != in {
			t.Errorf("%+v: %+v %v", in, x, ok)
		}
	}
	for _, o := range []Out{{}, {Unknown: true}, {Found: true, V: "v"}, {Found: true}} {
		if x, ok := DecOut(EncOut(o)); !ok || x != o {
			t.Errorf("%+v: %+v %v", o, x, ok)
		}
	}
	for _, b := range [][]byte{{}, {2}, {0, 1}, append(EncIn(In{K: "a"}), 0)} {
		if _, ok := DecIn(b); ok {
			t.Errorf("DecIn(%v)", b)
		}
	}
	for _, b := range [][]byte{{}, {0}, {2, 0}, {0, 2}} {
		if _, ok := DecOut(b); ok {
			t.Errorf("DecOut(%v)", b)
		}
	}
}

func op(c int, in In, o Out, call, ret int64) porcupine.Operation {
	return porcupine.Operation{ClientId: c, Input: in, Output: o, Call: call, Return: ret}
}

// The model: pending puts take effect at most once, later or never; a get sees the last put to
// take effect.
func TestModel(t *testing.T) {
	p := func(v string) In { return In{Put: true, K: "k", V: v} }
	g := In{K: "k"}
	got := func(v string) Out { return Out{Found: true, V: v} }
	unk := Out{Unknown: true}
	cases := []struct {
		ops []porcupine.Operation
		ok  bool
	}{
		{[]porcupine.Operation{op(0, g, Out{}, 0, 1)}, true},
		{[]porcupine.Operation{op(0, g, got("a"), 0, 1)}, false},
		{[]porcupine.Operation{op(0, p("a"), Out{}, 0, 1), op(1, g, got("a"), 2, 3)}, true},
		{[]porcupine.Operation{op(0, p("a"), Out{}, 0, 1), op(1, g, Out{}, 2, 3)}, false},
		// a pending put seen after a later known put
		{[]porcupine.Operation{op(0, p("a"), unk, 0, 1), op(1, p("b"), Out{}, 2, 3), op(1, g, got("a"), 4, 5)}, true},
		// a pending put takes effect once: a, b, a again is not possible
		{[]porcupine.Operation{op(0, p("a"), unk, 0, 1), op(1, g, got("a"), 2, 3), op(1, p("b"), Out{}, 4, 5),
			op(1, g, got("a"), 6, 7)}, false},
		// a pending put may never take effect
		{[]porcupine.Operation{op(0, p("a"), unk, 0, 1), op(1, g, Out{}, 2, 3)}, true},
		// keys are independent
		{[]porcupine.Operation{op(0, p("a"), Out{}, 0, 1), op(1, In{K: "j"}, Out{}, 2, 3)}, true},
		// a pending put seen after a later known put took effect last: the known put is gone
		{[]porcupine.Operation{op(0, p("a"), unk, 0, 1), op(1, p("b"), Out{}, 2, 3), op(1, g, got("a"), 4, 5),
			op(1, g, got("b"), 6, 7)}, false},
		// a put pending after the known state is still pending when the known state is seen again
		{[]porcupine.Operation{op(1, p("b"), Out{}, 0, 1), op(0, p("a"), unk, 2, 3), op(1, g, got("b"), 4, 5),
			op(1, g, got("a"), 6, 7)}, true},
		// an unknown get changes nothing
		{[]porcupine.Operation{op(0, g, unk, 0, 1), op(1, g, Out{}, 2, 3)}, true},
	}
	for i, c := range cases {
		if porcupine.CheckOperations(Model(), c.ops) != c.ok {
			t.Errorf("case %d: not %v", i, c.ok)
		}
	}
}

// Every node's addresses are distinct, and QuePaxa's configuration is the deployment's; every
// configuration choose can pick crosses the wire.
func TestConfig(t *testing.T) {
	seenA := map[string]bool{}
	for _, l := range [][]string{Addrs(), RecAddrs(), CfgAddrs(), ClientAddrs()} {
		for _, a := range l {
			if seenA[a] {
				t.Errorf("%s twice", a)
			}
			seenA[a] = true
		}
	}
	if uint64(len(Addrs())) != 1+NC+MaxReplicas || len(RecAddrs()) != len(Addrs()) ||
		len(CfgAddrs()) != len(Addrs()) || uint64(len(ClientAddrs())) != NC {
		t.Fatalf("address lists")
	}
	for _, n := range []uint64{3, 5} {
		cfg := config(n, Addrs(), RecAddrs())
		if len(cfg.Peers) != int(n) || uint64(len(cfg.Clients)) != NC {
			t.Fatalf("config: %+v", cfg)
		}
		for i, p := range cfg.Peers {
			if p.Name != strconv.Itoa(i+1) || p.IP+":"+p.PROXYPORT != Addrs()[NC+1+uint64(i)] ||
				p.IP+":"+p.RECORDERPORT != RecAddrs()[NC+1+uint64(i)] {
				t.Errorf("peer %d: %+v", i+1, p)
			}
		}
		for c, p := range cfg.Clients {
			if p.Name != strconv.Itoa(int(ClientName)+c) || p.IP+":"+p.CLIENTPORT != Addrs()[1+c] {
				t.Errorf("client %d: %+v", c, p)
			}
		}
	}
	seen := map[Conf]bool{}
	for i := 0; i < 20000; i++ {
		c := choose()
		d, ok := decode(c.encode())
		if !ok || d != c {
			t.Fatalf("%v: decoded %v, %v", c, d, ok)
		}
		seen[c] = true
	}
	if len(seen) != 2*2*5*5*8 {
		t.Errorf("choose picked %d configurations, not all %d", len(seen), 2*2*5*5*8)
	}
	for _, n := range []uint64{0, 7, 10, 21, 109, 12345} {
		if digits(n) != strconv.FormatUint(n, 10) {
			t.Errorf("digits(%d) = %q", n, digits(n))
		}
	}
}
