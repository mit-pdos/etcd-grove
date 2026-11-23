package epaxosnet

import (
	"bytes"
	"fmt"
	"io"
	"net"
	"os"
	"os/exec"
	"strconv"
	"sync"
	"testing"
	"time"

	"github.com/anishathalye/porcupine"
	"github.com/mit-pdos/etcd-grove/examples/lib/remote"
)

// The deployment on loopback, at the kit's own addresses: every machine but the orchestrator is
// this test binary run again (EPAXOSNET_NODE: "c<c>" client machine c, "s<id>" server machine id),
// each a process of its own (net/rpc's DefaultServer and net/http's DefaultServeMux are per
// process, as on the machines), in a directory of its own; the orchestrator is the test. Run it
// with the real net/rpc and net/http (go test) and with the models (a GOROOT of models/goroot.py
// farm, -tags netmodel). It takes about a minute (StartMs, then the operations).

func TestMain(m *testing.M) {
	if id := os.Getenv("EPAXOSNET_NODE"); id != "" {
		n, err := strconv.ParseUint(id[1:], 10, 64)
		if err != nil {
			panic(err)
		}
		if id[0] == 'c' {
			Client(n)
		} else {
			Server(n)
		}
		os.Exit(0)
	}
	os.Exit(m.Run())
}

// TestDeployment starts the server and client machines as processes and runs the orchestrator
// (Orch, its outputs counted): porcupine must accept the history and every operation be answered;
// no machine may end meanwhile.
func TestDeployment(t *testing.T) {
	if testing.Short() {
		t.Skip("the deployment takes about a minute")
	}
	exe, err := os.Executable()
	if err != nil {
		t.Fatal(err)
	}
	type exit struct {
		id  string
		out string
	}
	var nodes []string
	for id := uint64(1); id <= NReplicas+1; id++ {
		nodes = append(nodes, fmt.Sprintf("s%d", id))
	}
	for c := uint64(0); c < NC; c++ {
		nodes = append(nodes, fmt.Sprintf("c%d", c))
	}
	exited := make(chan exit, len(nodes))
	var cmds []*exec.Cmd
	for _, id := range nodes {
		cmd := exec.Command(exe, "-test.run=^$")
		cmd.Dir = t.TempDir()
		cmd.Env = append(os.Environ(), "EPAXOSNET_NODE="+id)
		var out bytes.Buffer
		cmd.Stdout = io.Discard
		cmd.Stderr = &out
		if err := cmd.Start(); err != nil {
			t.Fatal(err)
		}
		cmds = append(cmds, cmd)
		go func(id string) {
			cmd.Wait()
			exited <- exit{id, out.String()}
		}(id)
	}
	defer func() {
		for _, cmd := range cmds {
			cmd.Process.Kill()
		}
	}()
	// The client machines listen (a write's call is one attempt: a refused one is an unknown
	// outcome).
	for _, a := range ClientAddrs() {
		for {
			c, err := net.Dial("tcp", a)
			if err == nil {
				c.Close()
				break
			}
			time.Sleep(50 * time.Millisecond)
		}
	}
	t0 := time.Now()
	// Orch, with the outputs counted: in a run without faults every operation is answered.
	cd := Codec()
	var mu sync.Mutex
	known := 0
	dec := cd.DecOut
	cd.DecOut = func(b []byte) (any, bool) {
		o, ok := dec(b)
		if ok && !o.(Out).Unknown {
			mu.Lock()
			known++
			mu.Unlock()
		}
		return o, ok
	}
	if r := remote.Run(Model(), ClientAddrs(), cd, Gen, int(Ops), attempt(), 0); r != porcupine.Ok {
		t.Fatalf("porcupine: %v", r)
	}
	if known != int(NC*Ops) {
		t.Errorf("%d of %d operations answered", known, NC*Ops)
	}
	select {
	case e := <-exited:
		t.Fatalf("machine %s ended: %s", e.id, e.out)
	default:
	}
	if time.Since(t0) < time.Duration(StartMs)*time.Millisecond {
		t.Errorf("the orchestrator's calls did not reach the client machines")
	}
}

// TestModel checks the model's verdicts on small histories.
func TestModel(t *testing.T) {
	m := Model()
	op := func(c int, in In, o Out, t0, t1 int64) porcupine.Operation {
		return porcupine.Operation{ClientId: c, Input: in, Output: o, Call: t0, Return: t1}
	}
	put := func(k uint64, v string) In { return In{Op: OpPut, K: k, V: v} }
	get := func(k uint64) In { return In{Op: OpGet, K: k} }
	scan := func(k, n uint64) In { return In{Op: OpScan, K: k, N: n} }
	unk := Out{Unknown: true}
	cases := []struct {
		name string
		h    []porcupine.Operation
		ok   bool
	}{
		{"empty get", []porcupine.Operation{op(0, get(0), Out{}, 0, 1)}, true},
		{"phantom", []porcupine.Operation{op(0, get(0), Out{V: "a"}, 0, 1)}, false},
		{"put get", []porcupine.Operation{op(0, put(0, "a"), Out{}, 0, 1),
			op(1, get(0), Out{V: "a"}, 2, 3)}, true},
		{"stale", []porcupine.Operation{op(0, put(0, "a"), Out{}, 0, 1),
			op(1, get(0), Out{}, 2, 3)}, false},
		{"pending seen", []porcupine.Operation{op(0, put(0, "a"), unk, 0, 1),
			op(1, get(0), Out{V: "a"}, 2, 3)}, true},
		{"pending unseen", []porcupine.Operation{op(0, put(0, "a"), unk, 0, 1),
			op(1, get(0), Out{}, 2, 3)}, true},
		{"pending once", []porcupine.Operation{op(0, put(0, "a"), unk, 0, 1),
			op(1, get(0), Out{V: "a"}, 2, 3), op(2, put(0, "b"), Out{}, 4, 5),
			op(1, get(0), Out{V: "a"}, 6, 7)}, false},
		{"pending late", []porcupine.Operation{op(0, put(0, "a"), unk, 0, 1),
			op(2, put(0, "b"), Out{}, 2, 3), op(1, get(0), Out{V: "a"}, 4, 5)}, true},
		{"scan", []porcupine.Operation{op(0, put(0, "a1"), Out{}, 0, 1),
			op(0, put(1, "b1"), Out{}, 2, 3), op(1, scan(0, 1), Out{V: "a1b1"}, 4, 5)}, true},
		{"scan order", []porcupine.Operation{op(0, put(0, "a1"), Out{}, 0, 1),
			op(0, put(1, "b1"), Out{}, 2, 3), op(1, scan(0, 1), Out{V: "b1a1"}, 4, 5)}, false},
		{"scan pending", []porcupine.Operation{op(0, put(1, "b1"), unk, 0, 1),
			op(1, scan(0, 1), Out{V: "b1"}, 2, 3), op(2, get(1), Out{V: "b1"}, 4, 5)}, true},
		{"scan gap", []porcupine.Operation{op(0, put(1, "b1"), Out{}, 0, 1),
			op(1, scan(0, 2), Out{V: "b1"}, 2, 3)}, true},
	}
	for _, tc := range cases {
		if got := porcupine.CheckOperations(m, tc.h); got != tc.ok {
			t.Errorf("%s: got %v, want %v", tc.name, got, tc.ok)
		}
	}
}

// TestCodec checks that inputs and outputs cross the remote wire.
func TestCodec(t *testing.T) {
	cd := Codec()
	for c := 0; c < int(NC); c++ {
		for j := 0; j < 20; j++ {
			in := Gen(c)
			got, ok := cd.DecIn(cd.EncIn(in))
			if !ok || got.(In) != in {
				t.Errorf("input %v: got %v, %v", in, got, ok)
			}
		}
	}
	for _, o := range []Out{{}, {Unknown: true}, {V: "v12v34"}} {
		got, ok := cd.DecOut(cd.EncOut(o))
		if !ok || got.(Out) != o {
			t.Errorf("output %v: got %v, %v", o, got, ok)
		}
	}
}
