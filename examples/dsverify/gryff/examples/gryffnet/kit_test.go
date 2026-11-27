package gryffnet

import (
	"bytes"
	"fmt"
	"io"
	"math"
	"math/rand"
	"net"
	"os"
	"os/exec"
	"strconv"
	"sync"
	"sync/atomic"
	"testing"
	"time"

	"github.com/anishathalye/porcupine"
	"github.com/mit-pdos/etcd-grove/examples/lib/remote"
)

// The kit's deployment on loopback: the server machines and the client machines are this test
// binary re-executed (GRYFFNET_NODE: 1..1+NReplicas a server, 100+c client c), each in a directory
// of its own, at 127.0.0.1:(base+i) (a replica's net/rpc server 1000 above; client c's address
// base+2000+c). Separate processes, as the machines are: net/rpc's DefaultServer and http's
// DefaultServeMux are per process (a replica registers with them). The orchestrator is the test,
// running remote.Check with the loopback addresses.

func TestMain(m *testing.M) {
	if id := os.Getenv("GRYFFNET_NODE"); id != "" {
		n, err := strconv.ParseUint(id, 10, 64)
		if err != nil {
			panic(err)
		}
		base, err := strconv.ParseUint(os.Getenv("GRYFFNET_BASE"), 10, 64)
		if err != nil {
			panic(err)
		}
		servers := loopback(base, int(1+NReplicas))
		if n >= 100 {
			c := n - 100
			sys := newSys(servers, c)
			remote.ServeClient(int(c), loopback(base+2000, int(NC))[c],
				func(int) any { return sys }, Op, Codec(), attempt())
		}
		serve(n, servers)
		os.Exit(0)
	}
	os.Exit(m.Run())
}

// freeBase finds a port base b such that b+i, b+i+1000 and b+i+2000 (i < n) are free on loopback.
func freeBase(t *testing.T, n int) uint64 {
	for b := 20000 + rand.Intn(40000); b < 62000-n; b += 97 {
		ok := true
		var ls []net.Listener
		for i := 0; i < n && ok; i++ {
			for _, p := range []int{b + i, b + i + 1000, b + i + 2000} {
				l, err := net.Listen("tcp", fmt.Sprintf("127.0.0.1:%d", p))
				if err != nil {
					ok = false
					break
				}
				ls = append(ls, l)
			}
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

func loopback(base uint64, n int) []string {
	var addrs []string
	for i := 0; i < n; i++ {
		addrs = append(addrs, fmt.Sprintf("127.0.0.1:%d", base+uint64(i)))
	}
	return addrs
}

// deploy starts the server and client machines as processes, waits until the client machines
// listen, and returns their addresses and a check that no machine ended.
func deploy(t *testing.T) ([]string, func()) {
	n := int(1 + NReplicas + NC)
	base := freeBase(t, n)
	type exit struct {
		id  uint64
		err error
		out string
	}
	exited := make(chan exit, n)
	exe, err := os.Executable()
	if err != nil {
		t.Fatal(err)
	}
	var ids []uint64
	for id := uint64(1); id <= 1+NReplicas; id++ {
		ids = append(ids, id)
	}
	for c := uint64(0); c < NC; c++ {
		ids = append(ids, 100+c)
	}
	for _, id := range ids {
		cmd := exec.Command(exe, "-test.run=^$")
		cmd.Dir = t.TempDir()
		cmd.Env = append(os.Environ(), fmt.Sprintf("GRYFFNET_NODE=%d", id),
			fmt.Sprintf("GRYFFNET_BASE=%d", base))
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
		go func(id uint64) {
			err := cmd.Wait()
			exited <- exit{id, err, out.String()}
		}(id)
	}
	clients := loopback(base+2000, int(NC))
	for _, a := range clients {
		for start := time.Now(); ; {
			if c, err := net.Dial("tcp", a); err == nil {
				c.Close()
				break
			}
			if time.Since(start) > 30*time.Second {
				t.Fatalf("client machine %s does not listen", a)
			}
			time.Sleep(50 * time.Millisecond)
		}
	}
	return clients, func() {
		select {
		case e := <-exited:
			t.Fatalf("machine %d ended (%v):\n%s", e.id, e.err, e.out)
		default:
		}
	}
}

// TestDeployment runs the eleven machines (ten processes and the test as the orchestrator) and
// checks that the orchestrator's history is accepted (remote.Check panics otherwise) and that
// most operations got an answer.
func TestDeployment(t *testing.T) {
	addrs, ended := deploy(t)
	g := &gens{mu: new(sync.Mutex), n: make([]uint64, NC)}
	t0 := time.Now()
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
	r := remote.Run(Model(), addrs, cdc, func(c int) any { return g.next(c) }, int(K), attempt(), 0)
	if r != porcupine.Ok {
		t.Fatalf("porcupine: %v", r)
	}
	ended()
	t.Logf("%d of %d operations answered, in %v", known.Load(), NC*K, time.Since(t0))
	if known.Load() == 0 {
		t.Errorf("no operation was answered")
	}
}

// TestControlPhantom (the negative control): client machines whose reads return a value nobody
// wrote, as a register that invents values would, are caught.
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
		if in.(In).Op == OpRead {
			return Out{V: 987654321}
		}
		return Out{}
	}
	for c := range addrs {
		go remote.ServeClient(c, addrs[c], func(int) any { return nil }, phantom, Codec(), attempt())
	}
	time.Sleep(200 * time.Millisecond)
	g := &gens{mu: new(sync.Mutex), n: make([]uint64, NC)}
	if r := remote.Run(Model(), addrs, Codec(), func(c int) any { return g.next(c) }, int(K), attempt(), 0); r != porcupine.Illegal {
		t.Fatalf("porcupine: %v, want Illegal", r)
	}
}

// TestModel checks the model's verdicts on small histories.
func TestModel(t *testing.T) {
	m := Model()
	op := func(c int, in In, o Out, t0, t1 int64) porcupine.Operation {
		return porcupine.Operation{ClientId: c, Input: in, Output: o, Call: t0, Return: t1}
	}
	w := func(v int64) In { return In{Op: OpWrite, A: v} }
	cas := func(a, b int64) In { return In{Op: OpCAS, A: a, B: b} }
	rd := In{Op: OpRead}
	unk := Out{Unknown: true}
	cases := []struct {
		name string
		h    []porcupine.Operation
		ok   bool
	}{
		{"init", []porcupine.Operation{op(0, rd, Out{V: 0}, 0, 1)}, true},
		{"init bad", []porcupine.Operation{op(0, rd, Out{V: 1}, 0, 1)}, false},
		{"write read", []porcupine.Operation{op(0, w(5), Out{}, 0, 1), op(1, rd, Out{V: 5}, 2, 3)}, true},
		{"stale", []porcupine.Operation{op(0, w(5), Out{}, 0, 1), op(1, rd, Out{V: 0}, 2, 3)}, false},
		{"cas", []porcupine.Operation{op(0, w(5), Out{}, 0, 1), op(0, cas(5, 6), Out{}, 2, 3),
			op(1, rd, Out{V: 6}, 4, 5)}, true},
		{"cas no", []porcupine.Operation{op(0, w(5), Out{}, 0, 1), op(0, cas(4, 6), Out{}, 2, 3),
			op(1, rd, Out{V: 6}, 4, 5)}, false},
		{"pending late", []porcupine.Operation{op(0, w(5), unk, 0, 1), op(1, rd, Out{V: 0}, 2, 3),
			op(1, rd, Out{V: 5}, 4, 5)}, true},
		{"pending once", []porcupine.Operation{op(0, w(5), unk, 0, 1), op(1, rd, Out{V: 5}, 2, 3),
			op(1, w(7), Out{}, 4, 5), op(1, rd, Out{V: 5}, 6, 7)}, false},
		{"pending cas", []porcupine.Operation{op(0, w(5), Out{}, 0, 1), op(1, cas(5, 9), unk, 2, 3),
			op(0, w(5), Out{}, 4, 5), op(1, rd, Out{V: 9}, 6, 7)}, true},
		{"unknown read", []porcupine.Operation{op(0, rd, unk, 0, 1), op(1, rd, Out{V: 0}, 2, 3)}, true},
	}
	for _, tc := range cases {
		if got := porcupine.CheckOperations(m, tc.h); got != tc.ok {
			t.Errorf("%s: got %v, want %v", tc.name, got, tc.ok)
		}
	}
}

// Gen's inputs: per client a write, a read, a compare-and-swap, a read; values distinct and not 0.
func TestGen(t *testing.T) {
	seen := map[int64]bool{0: true}
	for c := uint64(0); c < NC; c++ {
		for j := uint64(0); j < K; j++ {
			in := Gen(c, j)
			switch j % 4 {
			case 0:
				if in.Op != OpWrite || seen[in.A] {
					t.Errorf("Gen(%d, %d) = %+v", c, j, in)
				}
				seen[in.A] = true
			case 2:
				if in.Op != OpCAS || seen[in.B] || in.A == 0 {
					t.Errorf("Gen(%d, %d) = %+v", c, j, in)
				}
				seen[in.B] = true
			default:
				if in.Op != OpRead {
					t.Errorf("Gen(%d, %d) = %+v", c, j, in)
				}
			}
		}
	}
}

// Op on a deployment where nothing listens: every operation's outcome is unknown.
func TestOpNoServer(t *testing.T) {
	servers := loopback(freeBase(t, int(1+NReplicas)), int(1+NReplicas))
	for c := uint64(0); c < NC; c++ {
		s := newSys(servers, c)
		s.started = true
		for j := uint64(0); j < K; j++ {
			if o := Op(s, Gen(c, j)); !o.(Out).Unknown {
				t.Errorf("Op(%d, %v) = %v with no server", c, Gen(c, j), o)
			}
		}
	}
}

// Every input and output crosses the remote wire: the codec gives back Gen's inputs, the extreme
// values' and the register's outputs, each within MaxLen.
func TestCodec(t *testing.T) {
	cdc := Codec()
	vals := []int64{0, 1, -1, math.MaxInt64, math.MinInt64, 1 << 32}
	var ins []In
	for c := uint64(0); c < NC; c++ {
		for j := uint64(0); j < K; j++ {
			ins = append(ins, Gen(c, j))
		}
	}
	outs := []Out{{}, {Unknown: true}}
	for _, a := range vals {
		ins = append(ins, In{Op: OpWrite, A: a})
		outs = append(outs, Out{V: a})
		for _, b := range vals {
			ins = append(ins, In{Op: OpCAS, A: a, B: b})
		}
	}
	for _, in := range ins {
		b := cdc.EncIn(in)
		if uint64(len(b)) > remote.MaxLen {
			t.Errorf("%+v: %d bytes", in, len(b))
		}
		if x, ok := cdc.DecIn(b); !ok || x.(In) != in {
			t.Errorf("%+v: decoded %v, %v", in, x, ok)
		}
	}
	for _, o := range outs {
		if x, ok := cdc.DecOut(cdc.EncOut(o)); !ok || x.(Out) != o {
			t.Errorf("%+v: decoded %v, %v", o, x, ok)
		}
	}
}
