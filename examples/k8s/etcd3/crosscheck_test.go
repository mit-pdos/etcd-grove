package etcd3

import (
	"bytes"
	"encoding/gob"
	"os"
	"testing"
	"time"

	"github.com/anishathalye/porcupine"
)

// crossChecked is the shared model m (SharedModel(revs, mode)) with every watch step it takes also
// checked by watchOk: each configuration stepIdx checks (the lazy one, and each of settle's) is
// recomputed here and both checks run on it, panicking if they differ. (Until 2026-11-28 this was
// the package variable crossCheck in stepIdx, G12: program code reads no mutable package variable.)
func crossChecked(m porcupine.Model, revs Revs, mode int) porcupine.Model {
	hh := &histHashes{}
	step := m.Step
	m.Step = func(st, input, output any) (bool, any) {
		in := input.(Input)
		out := output.(Output)
		if in.Kind == KWatch {
			check := func(d mcfg) bool {
				ok := watchOkIdx(in, out, d)
				if ok != watchOk(in, out, d) {
					panic("etcd3: watchOkIdx and watchOk differ")
				}
				return ok
			}
			b := bound(in, out)
			for _, c := range st.(state) {
				if mode == Lazy && check(hh.skipTo(c, target(in, out, c.st.rv))) {
					continue
				}
				for _, d := range settle(hh, revs, c, b, mode == Full, in, out) {
					check(hh.skipTo(d, target(in, out, d.st.rv)))
				}
			}
		}
		return step(st, input, output)
	}
	return m
}

// The history file examples/k8s/dist's dumpHistory writes (gob matches its fields by name).
type crossHistOp struct {
	ClientId     int
	Input        Input
	Output       Output
	Call, Return int64
}

type crossDump struct {
	R1, R2 uint64
	Ops    []crossHistOp
}

// TestCrossCheckWatches checks a store history examples/k8s/dist's RunStore dumped (DIST_DUMP; the
// file named by DIST_HISTORY) as CheckShared does, every watch step checked both by watchOk and by
// the shared model's indexed copy of it, which must agree (DIST_CHECK_TIMEOUT, a duration, is each
// mode's timeout; default 5m, CheckTimeout).
func TestCrossCheckWatches(t *testing.T) {
	p := os.Getenv("DIST_HISTORY")
	if p == "" {
		t.Skip("set DIST_HISTORY to a dumped history")
	}
	b, err := os.ReadFile(p)
	if err != nil {
		t.Fatal(err)
	}
	var d crossDump
	if err := gob.NewDecoder(bytes.NewReader(b)).Decode(&d); err != nil {
		t.Fatal(err)
	}
	ops := make([]porcupine.Operation, len(d.Ops))
	for i, o := range d.Ops {
		ops[i] = porcupine.Operation{ClientId: o.ClientId, Input: o.Input, Output: o.Output, Call: o.Call,
			Return: o.Return}
	}
	seeded := SeededAt(d.R1, d.R2)
	revs := HistoryRevs(ops)
	timeout := 5 * time.Minute
	if dd, err := time.ParseDuration(os.Getenv("DIST_CHECK_TIMEOUT")); err == nil {
		timeout = dd
	}
	for mode := Lazy; ; mode++ {
		r := porcupine.CheckOperationsTimeout(crossChecked(seeded.SharedModel(revs, mode), revs, mode), ops, timeout)
		t.Logf("%d operations, mode %d: %v", len(ops), mode, r)
		if r != porcupine.Illegal || mode == Full {
			break
		}
	}
}
