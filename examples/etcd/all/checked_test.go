package etcdall

import (
	"os"
	"testing"
	"time"

	"github.com/mit-pdos/etcd-grove/examples/lib/walarea"
)

// TestParamsOk (rule 38's non-vacuity test, part 1): ParamsOk agrees with the Lean premises it
// replaced (3 <= k5 <= 300) on TestMainRun's parameter and around both bounds.
func TestParamsOk(t *testing.T) {
	if !ParamsOk(3) {
		t.Fatal("TestMainRun's parameter is rejected")
	}
	for _, k := range []uint64{0, 1, 2, 3, 4, 150, 299, 300, 301, 1000, 1 << 63, ^uint64(0)} {
		if got, want := ParamsOk(k), 3 <= k && k <= 300; got != want {
			t.Fatalf("ParamsOk(%d) = %v, want %v", k, got, want)
		}
	}
}

// TestMainCheckedRun (rule 38's non-vacuity test, part 2): MainChecked on TestMainRun's parameter
// passes its check and runs the restart part (a failed check is a panic). Set ETCDALL_CHECKED=1 to run
// it (it starts the same clusters as TestMainRun).
func TestMainCheckedRun(t *testing.T) {
	if os.Getenv("ETCDALL_CHECKED") == "" {
		t.Skip("set ETCDALL_CHECKED=1")
	}
	t.Chdir(t.TempDir())
	walarea.ResetFamily(t, "restartN")
	walarea.Reset(t, "restart1")
	start := time.Now()
	MainChecked(3)
	t.Logf("MainChecked took %v", time.Since(start))
}
