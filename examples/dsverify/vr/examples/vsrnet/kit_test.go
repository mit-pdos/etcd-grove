package vsrnet

import (
	"net"
	"sync/atomic"
	"testing"
	"time"

	"github.com/anishathalye/porcupine"
	"github.com/mit-pdos/etcd-grove/examples/lib/remote"
)

// TestDeployment runs the twelve machines in one process (each at its own addresses; the real
// encoding/json and log/slog) and checks that the orchestrator's history is accepted. It runs
// Orch's steps with remote.Run in place of remote.Check (at the largest count Orch draws, Ops), to
// count the answered operations.
func TestDeployment(t *testing.T) {
	for id := uint64(1); id <= MaxReplicas; id++ {
		go Server(id)
	}
	for c := uint64(0); c < NC; c++ {
		go Client(c)
	}
	time.Sleep(200 * time.Millisecond)
	Configure(CfgAddrs(), choose())
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
	if r := remote.Run(Model(), ClientAddrs(), cdc, Gen, int(Ops), attempt(), 0); r != porcupine.Ok {
		t.Fatalf("porcupine: %v", r)
	}
	t.Logf("%d of %d operations answered", known.Load(), NC*Ops)
	if known.Load() == 0 {
		t.Errorf("no operation was answered")
	}
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
			return Out{Done: true}
		}
		return Out{Found: true, V: "phantom"}
	}
	for c := range addrs {
		go remote.ServeClient(c, addrs[c], func(int) any { return nil }, phantom, Codec(), attempt())
	}
	time.Sleep(200 * time.Millisecond)
	if r := remote.Run(Model(), addrs, Codec(), Gen, int(Ops), attempt(), 0); r != porcupine.Illegal {
		t.Fatalf("porcupine: %v, want Illegal", r)
	}
}

// TestModel checks the model's verdicts on small histories.
func TestModel(t *testing.T) {
	m := Model()
	op := func(c int, in In, o Out, t0, t1 int64) porcupine.Operation {
		return porcupine.Operation{ClientId: c, Input: in, Output: o, Call: t0, Return: t1}
	}
	put := func(k, v string) In { return In{Put: true, K: k, V: v} }
	get := func(k string) In { return In{K: k} }
	got := func(v string) Out { return Out{Found: true, V: v} }
	unk := Out{Unknown: true}
	done := Out{Done: true}
	cases := []struct {
		name string
		h    []porcupine.Operation
		ok   bool
	}{
		{"empty get", []porcupine.Operation{op(0, get("a"), Out{}, 0, 1)}, true},
		{"phantom", []porcupine.Operation{op(0, get("a"), got("x"), 0, 1)}, false},
		{"put get", []porcupine.Operation{op(0, put("a", "x"), done, 0, 1),
			op(1, get("a"), got("x"), 2, 3)}, true},
		{"stale", []porcupine.Operation{op(0, put("a", "x"), done, 0, 1),
			op(0, put("a", "y"), done, 2, 3), op(1, get("a"), got("x"), 4, 5)}, false},
		{"lost", []porcupine.Operation{op(0, put("a", "x"), done, 0, 1),
			op(1, get("a"), Out{}, 2, 3)}, false},
		{"concurrent", []porcupine.Operation{op(0, put("a", "x"), done, 0, 3),
			op(1, get("a"), got("x"), 1, 2)}, true},
		{"pending late", []porcupine.Operation{op(0, put("a", "x"), unk, 0, 1),
			op(1, get("a"), Out{}, 2, 3), op(1, get("a"), got("x"), 4, 5)}, true},
		{"pending once", []porcupine.Operation{op(0, put("a", "x"), unk, 0, 1),
			op(1, get("a"), got("x"), 2, 3), op(1, put("a", "y"), done, 4, 5),
			op(1, get("a"), got("x"), 6, 7)}, false},
		{"pending revives", []porcupine.Operation{op(0, put("a", "x"), unk, 0, 1),
			op(1, put("a", "y"), done, 2, 3), op(1, get("a"), got("x"), 4, 5)}, true},
		{"put answered as get", []porcupine.Operation{op(0, put("a", "x"), Out{}, 0, 1)}, false},
		{"get answered as put", []porcupine.Operation{op(0, get("a"), done, 0, 1)}, false},
		{"unknown get", []porcupine.Operation{op(0, get("a"), unk, 0, 1)}, true},
		{"keys", []porcupine.Operation{op(0, put("a", "x"), done, 0, 1),
			op(1, get("b"), got("x"), 2, 3)}, false},
	}
	for _, tc := range cases {
		if r := porcupine.CheckOperations(m, tc.h); r != tc.ok {
			t.Errorf("%s: got %v, want %v", tc.name, r, tc.ok)
		}
	}
}

// TestCodec checks that inputs and outputs decode to themselves.
func TestCodec(t *testing.T) {
	cd := Codec()
	for _, in := range []In{{Put: true, K: "k0", V: "v123"}, {K: "k1"}, {Put: true, K: "", V: ""}} {
		x, ok := cd.DecIn(cd.EncIn(in))
		if !ok || x.(In) != in {
			t.Errorf("input %v: %v %v", in, x, ok)
		}
	}
	for _, o := range []Out{{}, {Unknown: true}, {Done: true}, {Found: true, V: "v0"}} {
		x, ok := cd.DecOut(cd.EncOut(o))
		if !ok || x.(Out) != o {
			t.Errorf("output %v: %v %v", o, x, ok)
		}
	}
	for c := 0; c < int(NC); c++ {
		for j := 0; j < 50; j++ {
			in := Gen(c).(In)
			if in.Put && (in.V == "" || len(in.K) != 2) {
				t.Errorf("Gen(%d) = %v", c, in)
			}
		}
	}
}
