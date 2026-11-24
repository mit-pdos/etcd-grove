package craqnet

import (
	"os"
	"os/exec"
	"strconv"
	"testing"

	"github.com/anishathalye/porcupine"
)

// The deployment on loopback, one process per machine (net/rpc's DefaultServer and net/http's
// DefaultServeMux are a process's, and each server machine registers "RPC" with them): the client
// and server machines are this test binary re-executed (CRAQNET_MACHINE "client<c>" or
// "server<id>"), the orchestrator is the test. Run it with the real net/rpc and net/http (go test)
// and with the models (a GOROOT of models/goroot.py farm, go test -tags netmodel).

func TestMain(m *testing.M) {
	if w := os.Getenv("CRAQNET_MACHINE"); w != "" {
		if len(w) > 6 && w[:6] == "client" {
			c, err := strconv.ParseUint(w[6:], 10, 64)
			if err != nil {
				panic(err)
			}
			Client(c)
		}
		if len(w) > 6 && w[:6] == "server" {
			id, err := strconv.ParseUint(w[6:], 10, 64)
			if err != nil {
				panic(err)
			}
			Server(id)
		}
		os.Exit(0)
	}
	os.Exit(m.Run())
}

// start runs machine w (a CRAQNET_MACHINE value) as a process of its own.
func start(t *testing.T, w string) *exec.Cmd {
	cmd := exec.Command(os.Args[0], "-test.run=^$")
	cmd.Env = append(os.Environ(), "CRAQNET_MACHINE="+w)
	if testing.Verbose() {
		cmd.Stderr = os.Stderr
	}
	if err := cmd.Start(); err != nil {
		t.Fatal(err)
	}
	return cmd
}

// TestDeployment runs the machines and the orchestrator, which panics if porcupine rejects the
// history.
func TestDeployment(t *testing.T) {
	var cmds []*exec.Cmd
	for id := uint64(1); id <= MaxChain+1; id++ {
		cmds = append(cmds, start(t, "server"+strconv.FormatUint(id, 10)))
	}
	for c := uint64(0); c < NC; c++ {
		cmds = append(cmds, start(t, "client"+strconv.FormatUint(c, 10)))
	}
	defer func() {
		for _, cmd := range cmds {
			cmd.Process.Kill()
			cmd.Wait()
		}
	}()
	Orch()
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
	cases := []struct {
		name string
		h    []porcupine.Operation
		ok   bool
	}{
		{"empty get", []porcupine.Operation{op(0, get("a"), Out{}, 0, 1)}, true},
		{"phantom", []porcupine.Operation{op(0, get("a"), got("x"), 0, 1)}, false},
		{"put get", []porcupine.Operation{op(0, put("a", "x"), Out{}, 0, 1), op(1, get("a"), got("x"), 2, 3)}, true},
		{"stale", []porcupine.Operation{op(0, put("a", "x"), Out{}, 0, 1), op(1, get("a"), Out{}, 2, 3)}, false},
		{"concurrent", []porcupine.Operation{op(0, put("a", "x"), Out{}, 0, 3), op(1, get("a"), Out{}, 1, 2)}, true},
		{"other key", []porcupine.Operation{op(0, put("a", "x"), Out{}, 0, 1), op(1, get("b"), Out{}, 2, 3)}, true},
		{"pending seen", []porcupine.Operation{op(0, put("a", "x"), unk, 0, 1), op(1, get("a"), got("x"), 2, 3)}, true},
		{"pending unseen", []porcupine.Operation{op(0, put("a", "x"), unk, 0, 1), op(1, get("a"), Out{}, 2, 3)}, true},
		{"pending late", []porcupine.Operation{op(0, put("a", "x"), unk, 0, 1), op(1, put("a", "y"), Out{}, 2, 3),
			op(1, get("a"), got("x"), 4, 5)}, true},
		{"pending once", []porcupine.Operation{op(0, put("a", "x"), unk, 0, 1), op(1, get("a"), got("x"), 2, 3),
			op(1, put("a", "y"), Out{}, 4, 5), op(1, get("a"), got("x"), 6, 7)}, false},
		{"unknown get", []porcupine.Operation{op(0, get("a"), unk, 0, 1)}, true},
		{"before call", []porcupine.Operation{op(1, get("a"), got("x"), 0, 1), op(0, put("a", "x"), unk, 2, 3)}, false},
	}
	for _, tc := range cases {
		if r := porcupine.CheckOperations(m, tc.h); r != tc.ok {
			t.Errorf("%s: got %v, want %v", tc.name, r, tc.ok)
		}
	}
}

// TestConfCodec checks that decode inverts encode on the configurations and removals the
// orchestrator chooses.
func TestConfCodec(t *testing.T) {
	for i := 0; i < 1000; i++ {
		conf := choose()
		rs := plan(conf)
		for c := uint64(0); c < NC; c++ {
			m := mine(rs, c)
			if uint64(len(m)) > MaxRemovals {
				t.Fatalf("too many removals")
			}
			d, drs, ok := decode(conf.encode(m))
			if !ok || d != conf || len(drs) != len(m) {
				t.Fatalf("decode(encode(%v, %v)) = %v, %v, %v", conf, m, d, drs, ok)
			}
			for j := range m {
				if drs[j].Node != m[j].Node || drs[j].After != m[j].After {
					t.Fatalf("removal %d: %v, want %v", j, drs[j], m[j])
				}
			}
		}
	}
}
