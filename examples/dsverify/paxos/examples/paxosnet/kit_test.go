package paxosnet

import (
	"net"
	"sync/atomic"
	"testing"
	"time"

	"github.com/anishathalye/porcupine"
	"github.com/mit-pdos/etcd-grove/examples/lib/remote"
)

// TestDeployment runs the ten machines in one process (each at its own addresses) and checks
// that the orchestrator's history is accepted. It runs Orch's step with remote.Run in place of
// remote.Check (at the largest count Orch draws, Ops), to count the answered operations: a known
// answer shows the calls reached the client machines and paxos decided.
func TestDeployment(t *testing.T) {
	for id := uint64(1); id <= NAcceptors+NLearners; id++ {
		go Server(id)
	}
	for c := uint64(0); c < NC; c++ {
		go Client(c)
	}
	time.Sleep(500 * time.Millisecond)
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

// TestControlDisagree (the negative control): client machines that each answer their own
// proposal as decided, as a register without agreement would, are caught.
func TestControlDisagree(t *testing.T) {
	var addrs []string
	for c := uint64(0); c < NC; c++ {
		l, err := net.Listen("tcp", "127.0.0.1:0")
		if err != nil {
			t.Fatal(err)
		}
		addrs = append(addrs, l.Addr().String())
		l.Close()
	}
	own := func(sys any, in any) any { return Out{V: in.(string)} }
	for c := range addrs {
		go remote.ServeClient(c, addrs[c], func(int) any { return nil }, own, Codec(), attempt())
	}
	time.Sleep(200 * time.Millisecond)
	if r := remote.Run(Model(), addrs, Codec(), Gen, int(Ops), attempt(), 0); r != porcupine.Illegal {
		t.Fatalf("porcupine: %v, want Illegal", r)
	}
}

// TestModel checks the model's verdicts on small histories.
func TestModel(t *testing.T) {
	m := Model()
	call := func(c int, in string, o Out, t0, t1 int64) porcupine.Operation {
		return porcupine.Operation{ClientId: c, Input: in, Output: o, Call: t0, Return: t1}
	}
	cases := []struct {
		name string
		h    []porcupine.Operation
		ok   bool
	}{
		{"one", []porcupine.Operation{call(0, "a", Out{V: "a"}, 0, 1)}, true},
		{"other", []porcupine.Operation{call(0, "a", Out{V: "b"}, 0, 1)}, false},
		{"agree", []porcupine.Operation{call(0, "a", Out{V: "b"}, 0, 3),
			call(1, "b", Out{V: "b"}, 1, 2)}, true},
		{"disagree", []porcupine.Operation{call(0, "a", Out{V: "a"}, 0, 1),
			call(1, "b", Out{V: "b"}, 2, 3)}, false},
		{"pending", []porcupine.Operation{call(0, "a", Out{Unknown: true}, 0, 1),
			call(1, "b", Out{V: "a"}, 2, 3)}, true},
		{"late", []porcupine.Operation{call(0, "a", Out{V: "b"}, 0, 1),
			call(1, "b", Out{Unknown: true}, 2, 3)}, false},
	}
	for _, tc := range cases {
		if got := porcupine.CheckOperations(m, tc.h); got != tc.ok {
			t.Errorf("%s: got %v, want %v", tc.name, got, tc.ok)
		}
	}
}
