package paxosnet

import (
	"testing"
	"time"

	"github.com/anishathalye/porcupine"
)

// TestDeployment runs the ten machines in one process (each at its own addresses) and checks
// that the orchestrator's history is accepted (Orch panics otherwise), and that the calls
// reached the client machines (clients 2 and 3 wait StaggerMs before they propose).
func TestDeployment(t *testing.T) {
	for id := uint64(1); id <= NAcceptors+NLearners; id++ {
		go Server(id)
	}
	for c := uint64(0); c < NC; c++ {
		go Client(c)
	}
	time.Sleep(500 * time.Millisecond)
	t0 := time.Now()
	Orch()
	if time.Since(t0) < time.Duration(StaggerMs)*time.Millisecond {
		t.Errorf("the orchestrator's calls did not reach the client machines")
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
