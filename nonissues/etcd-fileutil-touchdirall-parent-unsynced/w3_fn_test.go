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
	"testing"

	"walspec/crashsim"
)

// TestW3FN: C-P3 (F-N1, F-N2). As TestCP3FirstStart, with the real Create and TouchDirAll.
func TestW3FN(t *testing.T) {
	for _, pre := range []bool{false, true} {
		t.Run(fmt.Sprintf("predirs=%v", pre), func(t *testing.T) {
			root := tempRoot(t)
			if pre {
				_, member, _ := layout(root)
				if err := os.MkdirAll(member, 0o700); err != nil {
					t.Fatal(err)
				}
			}
			sc := Script{Steps: []Step{
				{Op: "mkdirs"}, {Op: "create"},
				save([3]uint64{2, 1, 1}, ents3(1, 1, 2, 100)...),
				save([3]uint64{2, 1, 2}, ents3(2, 2, 2, 100)...),
			}}
			r := record(t, root, sc, nil, false)
			acked := map[string]int{}
			sum := r.Enumerate(t, Enum{Models: allModels, Seeds: 30}, tempRoot(t), func(v Verdict) {
				if v.Vanished && v.Ref.N >= 1 {
					acked[v.Spec.Model]++
				}
			})
			sum.Log(t, fmt.Sprintf("C-P3, real code (fixed=%v)", w3FixedFN()))
			t.Logf("images losing an acknowledged Save per model: %v", acked)
			lost := acked[crashsim.Posix] + acked[crashsim.Ordered] + acked[crashsim.Kill]
			if w3FixedFN() && lost > 0 {
				t.Errorf("C-P3 reached with the fixes")
			}
			if !w3FixedFN() && acked[crashsim.Posix] == 0 {
				t.Errorf("C-P3 not reached at the pin")
			}
		})
	}
}

func w3FixedFN() bool { return os.Getenv("W3_EXPECT") == "fixed" }
