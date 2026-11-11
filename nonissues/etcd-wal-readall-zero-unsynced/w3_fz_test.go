package walcrash

// A test of the WAL crash spec's ptrace record-and-replay harness (W0; module walspec, package
// walcrash: crashsim, walref, walharness, and hasStaleTail/markerTime in w0_test.go), which is not
// in this repository yet (it lands with examples/etcd/wal in the WAL spec's W4; until then
// /shared/tmp/wal-spec/go). Run in that package, with the module's go.mod replacing etcd by the
// fork at a4d2bb172 (fails) or 71f99a4bf with W3_EXPECT=fixed (passes):
//
//	go test ./walcrash/ -run TestW3 -v

// W3: the fork fixes' regression tests, against the real code (no modelled fix: fz=false, no
// fsyncdirs where the test is about directories). W3_EXPECT=fixed: the module replaces etcd by
// the fixed fork, every check must hold; otherwise (the pin): the bug must be reached.

import (
	"fmt"
	"os"
	"path/filepath"
	"testing"

	"walspec/crashsim"
	"walspec/walref"
)

func w3Fixed() bool { return os.Getenv("W3_EXPECT") == "fixed" }

// TestW3FZ: C-P5' (F-Z). As TestCP5Prime, with the real ReadAll (no modelled fdatasync).
func TestW3FZ(t *testing.T) {
	sc1 := Script{Steps: []Step{
		{Op: "mkdirs"}, {Op: "create"}, {Op: "fsyncdirs"},
		save([3]uint64{1, 1, 0}, ents3(1, 2, 1, 100)...),
		save([3]uint64{1, 1, 1}, ents3(3, 3, 1, 1000)...),
		{Op: "close"},
	}}
	r1 := record(t, tempRoot(t), sc1, nil, false)
	from := markerTime(t, r1, "B 4")
	to := markerTime(t, r1, "E 4 ")
	var starts []crashsim.Spec
	for k := from; k <= to; k++ {
		for seed := int64(1); seed <= 80 && len(starts) < 3; seed++ {
			s := crashsim.Spec{K: k, Model: crashsim.Posix, Seed: int64(k*100000) + seed}
			v := r1.Check(t, s, filepath.Join(tempRoot(t), "i"))
			if v.Out.Kind == walref.OK && len(v.Dec.Recs) == 3 && hasStaleTail(t, r1, s) {
				starts = append(starts, s)
			}
		}
	}
	if len(starts) == 0 {
		t.Fatal("no stale-tail image")
	}
	sc2 := Script{Steps: []Step{
		{Op: "restart"},
		save([3]uint64{1, 1, 3}, ents3(3, 3, 1, 1000)...),
		{Op: "close"},
	}}
	total := &Summary{}
	for _, s := range starts {
		r2 := continueFrom(t, r1, s, sc2, false)
		b2 := markerTime(t, r2, "B 1")
		e2 := markerTime(t, r2, "E 1 ")
		r2.Enumerate(t, Enum{Models: []string{crashsim.Posix, crashsim.Ordered}, Seeds: 40, From: b2}, tempRoot(t), func(v Verdict) {
			if v.Spec.K <= e2+1 {
				total.Add(v)
			}
		})
	}
	total.Log(t, fmt.Sprintf("C-P5' incarnation 2, real code (fixed=%v), from %d stale-tail images", w3Fixed(), len(starts)))
	bad := total.Unsound + total.RelBad
	if w3Fixed() && bad > 0 {
		t.Errorf("C-P5' reached with the fix: %d images", bad)
	}
	if !w3Fixed() && bad == 0 {
		t.Errorf("C-P5' not reached at the pin")
	}
}
