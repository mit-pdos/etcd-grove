package dist

import (
	"bytes"
	"encoding/gob"
	"os"

	"github.com/anishathalye/porcupine"

	k8s "github.com/mit-pdos/etcd-grove/examples/k8s/etcd3"
)

// dumpHistory writes the history ops (without the Raws, which the model does not read) to the file
// DIST_DUMP names, if any, suffixed with the process's id, with the seeds' revisions, for a check to
// be rerun or profiled offline (LoadHistory, TestReplayHistory): the store orchestrator's
// Observer.History in the test's processes (test-only since 2026-11-27, G4: gob has no model).
func dumpHistory(seeded k8s.Seeded, ops []porcupine.Operation) {
	p := os.Getenv("DIST_DUMP")
	if p == "" {
		return
	}
	h := make([]HistOp, len(ops))
	for i, op := range ops {
		out := op.Output.(k8s.Output)
		out.Raw = k8s.Raw{}
		h[i] = HistOp{ClientId: op.ClientId, Input: op.Input.(k8s.Input), Output: out, Call: op.Call,
			Return: op.Return}
	}
	var b bytes.Buffer
	r1, r2 := seeded.SeedRevs()
	if gob.NewEncoder(&b).Encode(dump{R1: r1, R2: r2, Ops: h}) == nil {
		os.WriteFile(p+"."+itoa(os.Getpid()), b.Bytes(), 0o644)
	}
}

// A HistOp is a store operation as dumpHistory writes it.
type HistOp struct {
	ClientId     int
	Input        k8s.Input
	Output       k8s.Output
	Call, Return int64
}

type dump struct {
	R1, R2 uint64
	Ops    []HistOp
}

// LoadHistory reads a history dumpHistory wrote, with its seeded store.
func LoadHistory(p string) (k8s.Seeded, []porcupine.Operation, error) {
	b, err := os.ReadFile(p)
	if err != nil {
		return k8s.Seeded{}, nil, err
	}
	var d dump
	if err := gob.NewDecoder(bytes.NewReader(b)).Decode(&d); err != nil {
		return k8s.Seeded{}, nil, err
	}
	h := d.Ops
	ops := make([]porcupine.Operation, len(h))
	for i, o := range h {
		ops[i] = porcupine.Operation{ClientId: o.ClientId, Input: o.Input, Output: o.Output, Call: o.Call,
			Return: o.Return}
	}
	return k8s.SeededAt(d.R1, d.R2), ops, nil
}
