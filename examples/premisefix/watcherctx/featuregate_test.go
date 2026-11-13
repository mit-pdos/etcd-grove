package watcherctx

// T5-c: the default feature gate's Set(s ++ "=true") (k8s.io/component-base cd2c1afd246a
// featuregate/feature_gate.go: Set -> SetFromMapWithLogger, :361, :481-511), and the restated
// environment assumption of Proof/k8s_io/apiserver/pkg/util/feature/Gate.lean: no code mutates the
// gate but Sets of the one value its table k8sSetValue gives each feature (repeats harmless), each
// before any Enabled of its feature (checked by etc/featuregate-check.py).
//
// The gate is process-global state, so each scenario runs in a process of its own (the test binary
// re-run with WATCHERCTX_SCENARIO set).
//
//   - watchlist-true: Set("WatchList=true") returns nil and Enabled("WatchList") is true, also from
//     8 goroutines (800 calls): featureOn's law.
//   - two-features: Set("EtcdRangeStream=false") then Set("WatchList=true"): both values hold
//     afterwards (a Set of another feature keeps an earlier one: SetFromMapWithLogger re-applies
//     enabledRaw, every earlier pair), so featureOff and featureOn are both persistent.
//   - true-then-false (what the table excludes: Set has a spec for one value per feature): a second
//     Set of the same feature to the other value changes Enabled; featureOn would then be false.
//   - enabled-then-set (what the assumption excludes): Enabled before Set answers the default at
//     the emulated version (true for WatchList at the pin's binary version, 1.34+), and a later
//     Set(false) changes it; a caller that branched on the first answer saw a value no fact gave.
//   - enabled-kept-then-set (what the "before any Enabled" clause excludes, with the table's value):
//     Enabled(EtcdRangeStream) answers true, then Set("EtcdRangeStream=false") succeeds; a caller
//     that kept Enabled's wand would derive true = false.
//   - failed-set: Set of a feature locked to its default (DeclarativeValidation, GA and locked in
//     1.36) errs and Enabled("WatchList") is unchanged; a later Set("WatchList=true") errs too (the
//     failed Set's raw pair poisons later Sets, :500-504): the triple's error arm, nothing given.

import (
	"os"
	"os/exec"
	"sync"
	"testing"

	"k8s.io/apiserver/pkg/features"
	utilfeature "k8s.io/apiserver/pkg/util/feature"
	"k8s.io/component-base/featuregate"
)

const scenarioEnv = "WATCHERCTX_SCENARIO"

func TestGateScenarios(t *testing.T) {
	if os.Getenv(scenarioEnv) != "" {
		t.Skip("in a scenario process")
	}
	for _, sc := range []string{"watchlist-true", "two-features", "true-then-false", "enabled-then-set", "enabled-kept-then-set", "failed-set"} {
		cmd := exec.Command(os.Args[0], "-test.run=^TestGateScenario$", "-test.v", "-test.count=1")
		cmd.Env = append(os.Environ(), scenarioEnv+"="+sc)
		out, err := cmd.CombinedOutput()
		if err != nil {
			t.Errorf("scenario %s failed: %v\n%s", sc, err, out)
		} else {
			t.Logf("scenario %s passed", sc)
		}
	}
}

func enabled(f featuregate.Feature) bool { return utilfeature.DefaultFeatureGate.Enabled(f) }

func set(s string) error { return utilfeature.DefaultMutableFeatureGate.Set(s) }

func TestGateScenario(t *testing.T) {
	sc := os.Getenv(scenarioEnv)
	if sc == "" {
		t.Skip("run by TestGateScenarios")
	}
	switch sc {
	case "watchlist-true":
		if err := set("WatchList=true"); err != nil {
			t.Fatal(err)
		}
		var wg sync.WaitGroup
		var mu sync.Mutex
		bad := 0
		for g := 0; g < 8; g++ {
			wg.Add(1)
			go func() {
				defer wg.Done()
				for i := 0; i < 100; i++ {
					if !enabled(features.WatchList) {
						mu.Lock()
						bad++
						mu.Unlock()
					}
				}
			}()
		}
		wg.Wait()
		if bad != 0 {
			t.Fatalf("%d of 800 Enabled(WatchList) calls returned false after Set(WatchList=true)", bad)
		}
	case "two-features":
		if err := set("EtcdRangeStream=false"); err != nil {
			t.Fatal(err)
		}
		if err := set("WatchList=true"); err != nil {
			t.Fatal(err)
		}
		if enabled(features.EtcdRangeStream) || !enabled(features.WatchList) {
			t.Fatalf("EtcdRangeStream %v (want false), WatchList %v (want true)",
				enabled(features.EtcdRangeStream), enabled(features.WatchList))
		}
	case "true-then-false":
		if err := set("WatchList=true"); err != nil || !enabled(features.WatchList) {
			t.Fatalf("first Set: %v, Enabled %v", err, enabled(features.WatchList))
		}
		if err := set("WatchList=false"); err != nil {
			t.Fatal(err)
		}
		if enabled(features.WatchList) {
			t.Fatal("a second Set did not change Enabled; the assumption would be unnecessary")
		}
		t.Log("a second Set of the same feature changes Enabled: excluded by the assumption")
	case "enabled-then-set":
		before := enabled(features.WatchList)
		if !before {
			t.Fatal("WatchList's default at the binary version is expected true (1.34+)")
		}
		if err := set("WatchList=false"); err != nil {
			t.Fatal(err)
		}
		if enabled(features.WatchList) {
			t.Fatal("Set after Enabled did not take effect")
		}
		t.Log("Enabled before Set answered the default, and a later Set changed it: excluded by the assumption")
	case "enabled-kept-then-set":
		// The table's own value (EtcdRangeStream=false), after an Enabled: the program
		//   b := Enabled(EtcdRangeStream); if Set("EtcdRangeStream=false") == nil && b { panic }
		// panics in Go, yet without the "before any Enabled" clause its no-panic triple would be
		// provable (Enabled's caller keeps the wand featureOff -∗ ⌜b = false⌝ and applies it to the
		// featureOff Set gives). So the clause stays (k8s 7f-5 S1 review).
		b := enabled(features.EtcdRangeStream)
		if !b {
			t.Fatal("EtcdRangeStream's default at the binary version is expected true (1.37+)")
		}
		if set("EtcdRangeStream=false") != nil {
			t.Fatal("Set(EtcdRangeStream=false) failed")
		}
		if enabled(features.EtcdRangeStream) {
			t.Fatal("Set after Enabled did not take effect")
		}
		t.Log("the kept answer is true, the Set succeeded: the program above would panic; excluded by the assumption")
	case "failed-set":
		before := enabled(features.WatchList)
		if err := set("DeclarativeValidation=false"); err == nil {
			t.Fatal("Set of a feature locked to its default succeeded")
		}
		if enabled(features.WatchList) != before {
			t.Fatal("a failed Set changed Enabled(WatchList)")
		}
		if err := set("WatchList=true"); err == nil {
			t.Log("note: a later Set succeeded (no poisoning at this pin)")
		} else {
			t.Logf("a later Set errs too (poisoned): %v", err)
		}
	default:
		t.Fatalf("unknown scenario %q", sc)
	}
}
