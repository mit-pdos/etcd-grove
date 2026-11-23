package rabianet

import (
	"bytes"
	"fmt"
	"io"
	"os"
	"os/exec"
	"strconv"
	"sync/atomic"
	"testing"
	"time"

	"github.com/anishathalye/porcupine"
	"github.com/mit-pdos/etcd-grove/examples/lib/remote"
	"rabia/internal/config"
)

// The kit's deployment on loopback: every machine but the orchestrator is this test binary
// re-executed (RABIANET_NODE: 1..NC client machine NODE-1, NC+1..NC+MaxServers server machine
// NODE-NC), one process per machine, since Rabia's configuration is a process global. The
// orchestrator is the test, running Orch.
func TestMain(m *testing.M) {
	if id := os.Getenv("RABIANET_NODE"); id != "" {
		n, err := strconv.ParseUint(id, 10, 64)
		if err != nil {
			panic(err)
		}
		if n <= NC {
			Client(n - 1)
		}
		Server(n - NC)
		os.Exit(0)
	}
	os.Exit(m.Run())
}

// deploy starts the client and server machines as processes and returns a check that none ended.
func deploy(t *testing.T) func() {
	type exit struct {
		id  uint64
		err error
		out string
	}
	exited := make(chan exit, NC+MaxServers)
	for id := uint64(1); id <= NC+MaxServers; id++ {
		cmd := exec.Command(os.Args[0], "-test.run=^$")
		cmd.Env = append(os.Environ(), fmt.Sprintf("RABIANET_NODE=%d", id))
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
	return func() {
		select {
		case e := <-exited:
			t.Fatalf("machine %d ended (%v):\n%s", e.id, e.err, e.out)
		default:
		}
	}
}

// TestDeployment runs the twelve machines (the orchestrator in the test's process) and checks
// that the orchestrator's history is accepted (Orch panics otherwise) and that no machine ended.
// It runs Orch's steps with remote.Run in place of remote.Check, to count the answered operations.
func TestDeployment(t *testing.T) {
	check := deploy(t)
	New()
	time.Sleep(time.Duration(StartMs) * time.Millisecond)
	var known atomic.Int64
	m := Model()
	cdc := Codec()
	dec := cdc.DecOut
	cdc.DecOut = func(b []byte) (any, bool) {
		o, ok := dec(b)
		if ok && !o.(Out).Unknown {
			known.Add(1)
		}
		return o, ok
	}
	if r := remote.Run(m, ClientAddrs(), cdc, gens(), int(K), attempt(), 0); r != porcupine.Ok {
		t.Fatalf("porcupine: %v", r)
	}
	check()
	t.Logf("%d of %d operations answered", known.Load(), NC*K)
	if known.Load() == 0 {
		t.Errorf("no operation was answered")
	}
}

// TestModel checks the model's verdicts on small histories.
func TestModel(t *testing.T) {
	m := Model()
	call := func(c int, in In, o Out, t0, t1 int64) porcupine.Operation {
		return porcupine.Operation{ClientId: c, Input: in, Output: o, Call: t0, Return: t1}
	}
	put := func(k, v string) In { return In{Put: true, K: k, V: v} }
	get := func(k string) In { return In{K: k} }
	got := func(v string) Out { return Out{Found: v != "", V: v} }
	done := Out{Put: true}
	unk := Out{Unknown: true}
	cases := []struct {
		name string
		h    []porcupine.Operation
		ok   bool
	}{
		{"empty", []porcupine.Operation{call(0, get("a"), got(""), 0, 1)}, true},
		{"phantom", []porcupine.Operation{call(0, get("a"), got("x"), 0, 1)}, false},
		{"put get", []porcupine.Operation{call(0, put("a", "x"), done, 0, 1), call(1, get("a"), got("x"), 2, 3)}, true},
		{"stale", []porcupine.Operation{call(0, put("a", "x"), done, 0, 1), call(1, get("a"), got(""), 2, 3)}, false},
		{"other key", []porcupine.Operation{call(0, put("a", "x"), done, 0, 1), call(1, get("b"), got(""), 2, 3)}, true},
		{"pending", []porcupine.Operation{call(0, put("a", "x"), unk, 0, 1), call(1, get("a"), got("x"), 2, 3)}, true},
		{"pending not yet", []porcupine.Operation{call(0, put("a", "x"), unk, 0, 1), call(1, get("a"), got(""), 2, 3)}, true},
		{"pending once", []porcupine.Operation{call(0, put("a", "x"), unk, 0, 1), call(1, get("a"), got("x"), 2, 3),
			call(1, put("a", "y"), done, 4, 5), call(1, get("a"), got("x"), 6, 7)}, false},
		{"pending late", []porcupine.Operation{call(0, put("a", "x"), unk, 0, 1), call(1, put("a", "y"), done, 2, 3),
			call(1, get("a"), got("x"), 4, 5)}, true},
		{"unknown get", []porcupine.Operation{call(0, get("a"), unk, 0, 1)}, true},
	}
	for _, tc := range cases {
		if got := porcupine.CheckOperations(m, tc.h); got != tc.ok {
			t.Errorf("%s: got %v, want %v", tc.name, got, tc.ok)
		}
	}
}

// TestGen: Gen's keys are KeyLen bytes ("key00000", "key00001", Rabia's Conf.KeyLen), a round's
// put and get share a key, put values are distinct and non-empty, and each key gets a quarter of
// the rounds or more.
func TestGen(t *testing.T) {
	configure(nil, Conf{N: 3, F: 1})
	if uint64(config.Conf.KeyLen) != KeyLen {
		t.Fatalf("Conf.KeyLen = %d, KeyLen = %d", config.Conf.KeyLen, KeyLen)
	}
	seen := map[string]bool{}
	rounds := map[string]int{}
	for c := uint64(0); c < NC; c++ {
		for j := uint64(0); j < K; j++ {
			in := Gen(c, j)
			if uint64(len(in.K)) != KeyLen || (in.K != "key00000" && in.K != "key00001") {
				t.Errorf("Gen(%d, %d) = %+v: key", c, j, in)
			}
			if in.Put != (j%2 == 0) || (in.Put && (seen[in.V] || in.V == "")) {
				t.Errorf("Gen(%d, %d) = %+v", c, j, in)
			}
			seen[in.V] = true
			if j%2 == 0 {
				rounds[in.K]++
			} else if in.K != Gen(c, j-1).K {
				t.Errorf("Gen(%d, %d) = %+v: not the put's key", c, j, in)
			}
		}
	}
	for _, k := range []string{"key00000", "key00001"} {
		if 4*uint64(rounds[k]) < NC*(K/2) {
			t.Errorf("Gen's rounds per key: %v", rounds)
		}
	}
	g := gens()
	for j := uint64(0); j < K; j++ {
		if g(1).(In) != Gen(1, j) {
			t.Errorf("gens: client 1's input %d", j)
		}
	}
}

// TestCodec: inputs and outputs cross the remote wire.
func TestCodec(t *testing.T) {
	cdc := Codec()
	ins := []In{{}, {Put: true, K: "key00000", V: "v00"}, {K: "\xff\x00"}, {Put: true, K: "", V: "x"}}
	for _, in := range ins {
		if x, ok := cdc.DecIn(cdc.EncIn(in)); !ok || x.(In) != in {
			t.Errorf("%+v: decoded %v %v", in, x, ok)
		}
	}
	outs := []Out{{Unknown: true}, {Put: true}, {Found: true, V: "v"}, {}}
	for _, o := range outs {
		if x, ok := cdc.DecOut(cdc.EncOut(o)); !ok || x.(Out) != o {
			t.Errorf("%+v: decoded %v %v", o, x, ok)
		}
	}
	for _, b := range [][]byte{{}, {2}, {1, 9, 0, 0, 0, 0, 0, 0, 0}} {
		if _, ok := cdc.DecIn(b); ok {
			t.Errorf("DecIn(%v)", b)
		}
	}
}

// TestConfig: every configuration choose can pick crosses the wire, and configure sets Rabia's
// Conf from it.
func TestConfig(t *testing.T) {
	seen := map[Conf]bool{}
	for i := 0; i < 50000; i++ {
		c := choose()
		d, ok := decode(c.encode())
		if !ok || d != c {
			t.Fatalf("%v: decoded %v, %v", c, d, ok)
		}
		seen[c] = true
	}
	if len(seen) != 3*NBatches*NBatchMs*NBlocks {
		t.Errorf("choose picked %d configurations, not all %d", len(seen), 3*NBatches*NBatchMs*NBlocks)
	}
	for _, b := range [][]byte{{0, 0, 0, 0, 0}, {4, 1, 0, 0, 0}, {3, 0, 0, 0, 0}, {3, 2, 0, 0, 0}, {5, 3, 0, 0, 0},
		{3, 1, NBatches, 0, 0}, {3, 1, 0, NBatchMs, 0}, {5, 2, 0, 0, NBlocks}, {255, 255, 255, 255, 255}} {
		if c, ok := decode(b); ok {
			t.Errorf("decode(%v) = %v", b, c)
		}
	}
	for c := range seen {
		configure(NetAddrs()[:c.N], c)
		k := config.Conf
		if uint64(k.NServers) != c.N || uint64(k.NFaulty) != c.F || len(k.Peers) != int(c.N) ||
			uint64(k.ProxyBatchSize) != batchSize(c.Batch) || uint64(k.LenBlockArray) != blocks(c.Blocks) ||
			uint64(k.ProxyBatchTimeout.Milliseconds()) != batchMs(c.BatchMs) || k.NMinusF != int(c.N-c.F) ||
			k.LenLedger != 10000 || k.KeyLen != int(KeyLen) {
			t.Errorf("configure(%v): %+v", c, k)
		}
	}
	for _, n := range []uint64{0, 7, 10, 21, 109, 12345} {
		if digits(n) != strconv.FormatUint(n, 10) {
			t.Errorf("digits(%d) = %q", n, digits(n))
		}
	}
}
