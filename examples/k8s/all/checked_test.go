package k8sall

import (
	"math/big"
	"math/rand"
	"os"
	"testing"
	"time"

	"github.com/mit-pdos/etcd-grove/examples/lib/walarea"
)

func paramsOkRef(k1 uint64, c, o, w, wo int, k2 uint64) bool {
	if !(1 <= k1 && k1 <= 1000 && 1 <= k2 && k2 <= 600 && 0 <= c && 0 <= w && 0 <= o && 0 <= wo) {
		return false
	}
	if new(big.Int).Add(big.NewInt(int64(c)), big.NewInt(int64(w))).Cmp(big.NewInt(1<<31)) >= 0 {
		return false
	}
	s := new(big.Int).Mul(big.NewInt(int64(c)), big.NewInt(int64(o)))
	s.Add(s, new(big.Int).Mul(big.NewInt(int64(w)), big.NewInt(int64(wo))))
	return s.Cmp(new(big.Int).Lsh(big.NewInt(1), 60)) < 0
}

// TestParamsOk (rule 38's non-vacuity test, part 1): ParamsOk agrees with the exact premises on
// TestMain's parameters and on random parameters near and across every bound.
func TestParamsOk(t *testing.T) {
	if !ParamsOk(3, 4, 60, 0, 0, 3) {
		t.Fatal("TestMain's parameters are rejected")
	}
	pick := func(edges ...int64) int {
		return int(edges[rand.Intn(len(edges))] + int64(rand.Intn(3)) - 1)
	}
	for i := 0; i < 200000; i++ {
		k1, k2 := uint64(pick(0, 1, 1000, 3)), uint64(pick(0, 1, 600, 3))
		c, w := pick(0, 4, 1<<30, 1<<31), pick(0, 1, 1<<30, 1<<31)
		o, wo := pick(0, 60, 1<<29, 1<<30, 1<<31, 1<<32), pick(0, 1, 1<<29, 1<<30, 1<<31)
		if got, want := ParamsOk(k1, c, o, w, wo, k2), paramsOkRef(k1, c, o, w, wo, k2); got != want {
			t.Fatalf("ParamsOk(%d %d %d %d %d %d) = %v, want %v", k1, c, o, w, wo, k2, got, want)
		}
	}
}

// TestMainCheckedRun (part 2): MainChecked on TestMain's parameters, with random schedules,
// passes its check and runs both workloads (a failed check is a panic). Set K8SALL_CHECKED=1.
func TestMainCheckedRun(t *testing.T) {
	if os.Getenv("K8SALL_CHECKED") == "" {
		t.Skip("set K8SALL_CHECKED=1")
	}
	t.Chdir(t.TempDir())
	walarea.ResetFamily(t, "k8setcd3N", "k8scompactorN")
	start := time.Now()
	MainChecked(3, 4, 60, 0, 0, 4, 3, 4)
	t.Logf("MainChecked took %v", time.Since(start))
}
