package etcdall

import (
	"math/big"
	"math/rand"
	"os"
	"testing"
	"time"

	"github.com/mit-pdos/etcd-grove/examples/lib/walarea"
)

// paramsOkRef is ParamsOk computed exactly (big integers): the Lean premises it replaces.
func paramsOkRef(k1 uint64, c, o, nw, nops, cnw, cnops int, k2, k3, k4, k5 uint64) bool {
	lt := func(a, b int, bound uint) bool {
		p := new(big.Int).Mul(big.NewInt(int64(a)), big.NewInt(int64(b)))
		return p.Cmp(new(big.Int).Lsh(big.NewInt(1), bound)) < 0
	}
	in := func(x, lo, hi uint64) bool { return lo <= x && x <= hi }
	return in(k1, 1, 1000) && 0 <= c && c < 1<<31 && 0 <= o && lt(c, o, 60) &&
		0 <= nw && nw < 1<<31 && 0 <= nops && lt(nw, nops, 62) &&
		0 <= cnw && cnw < 1<<31 && 0 <= cnops && lt(cnw, cnops, 62) &&
		in(k2, 1, 300) && in(k3, 1, 300) && in(k4, 1, 300) && in(k5, 3, 300)
}

// TestParamsOk (rule 38's non-vacuity test, part 1): ParamsOk agrees with the exact premises on the
// parameters TestMainRun uses, on random parameters near and across every bound, and on the
// products' boundary cases.
func TestParamsOk(t *testing.T) {
	if !ParamsOk(3, 3, 150, 3, 300, 4, 25, 3, 3, 3, 3) {
		t.Fatal("TestMainRun's parameters are rejected")
	}
	pick := func(edges ...int64) int {
		e := edges[rand.Intn(len(edges))]
		return int(e + int64(rand.Intn(3)) - 1)
	}
	for i := 0; i < 200000; i++ {
		ks := func(lo, hi int64) uint64 { return uint64(pick(0, lo, hi, 2)) }
		k1, k2, k3, k4, k5 := ks(1, 1000), ks(1, 300), ks(1, 300), ks(1, 300), ks(3, 300)
		c, o := pick(0, 1, 3, 1<<31, 1<<30, 1<<29), pick(0, 1, 150, 1<<30, 1<<31, 1<<32)
		nw, nops := pick(0, 3, 1<<31, 1<<30), pick(0, 300, 1<<32, 1<<31, 1<<33)
		cnw, cnops := pick(0, 4, 1<<31), pick(0, 25, 1<<31, 1<<32)
		if got, want := ParamsOk(k1, c, o, nw, nops, cnw, cnops, k2, k3, k4, k5),
			paramsOkRef(k1, c, o, nw, nops, cnw, cnops, k2, k3, k4, k5); got != want {
			t.Fatalf("ParamsOk(%d %d %d %d %d %d %d %d %d %d %d) = %v, want %v",
				k1, c, o, nw, nops, cnw, cnops, k2, k3, k4, k5, got, want)
		}
	}
}

// TestMainCheckedRun (rule 38's non-vacuity test, part 2): MainChecked on TestMainRun's parameters,
// with random schedules as long as TestMainRun's, passes its check and runs every part (a failed
// check is a panic). Set ETCDALL_CHECKED=1 to run it (it starts the same clusters as TestMainRun).
func TestMainCheckedRun(t *testing.T) {
	if os.Getenv("ETCDALL_CHECKED") == "" {
		t.Skip("set ETCDALL_CHECKED=1")
	}
	t.Chdir(t.TempDir())
	walarea.ResetFamily(t, "txnlinfaultsN", "linkv3p", "authN", "authlease", "leaseN",
		"leasecatchup", "restartN")
	walarea.Reset(t, "compactkv", "putgetc", "cachekv", "restart1")
	start := time.Now()
	MainChecked(3, 3, 150, len(schedule(3)), 3, 300, len(schedule(3)), 4, 25, 3, 3, 3, 3)
	t.Logf("MainChecked took %v", time.Since(start))
}
