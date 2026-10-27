package dsmain

import (
	"os"
	"strconv"
	"testing"

	"github.com/go-logr/logr"
	"k8s.io/klog/v2"
)

// envInt is the environment variable's value, or def.
func envInt(name string, def int) int {
	n, err := strconv.Atoi(os.Getenv(name))
	if err != nil || n <= 0 {
		return def
	}
	return n
}

// TestMain drops klog's output (the controller and the reflectors log every injected failure),
// once: the goroutines of a finished run (informers, the controller's workers) still read the
// logger while they wind down.
func TestMain(m *testing.M) {
	klog.SetLogger(logr.Discard())
	os.Exit(m.Run())
}

// TestMainNeverPanics runs Main DSMAIN_RUNS times (default 20), each with DSMAIN_CHECKS checks
// (default 2000, about two and a half seconds under -race); a panic fails the test.
func TestMainNeverPanics(t *testing.T) {
	runs, checks := envInt("DSMAIN_RUNS", 20), envInt("DSMAIN_CHECKS", 2000)
	for i := 0; i < runs; i++ {
		Main(checks)
	}
	t.Logf("Main(%d): %d runs, no panic", checks, runs)
}

// TestScheduled: the scenario is not vacuous: its runs (Main's, through run) end with the
// DaemonSet's pod on the node, given time (DSMAIN_SCHEDULED_RUNS, default 20).
func TestScheduled(t *testing.T) {
	runs, checks := envInt("DSMAIN_SCHEDULED_RUNS", 20), envInt("DSMAIN_CHECKS", 2000)
	scheduled := 0
	for i := 0; i < runs; i++ {
		if run(serverConfig(), checks) == 1 {
			scheduled++
		}
	}
	t.Logf("%d of %d runs ended with the DaemonSet's pod bound to the node", scheduled, runs)
	if scheduled == 0 {
		t.Errorf("no run ever had the DaemonSet's pod on the node")
	}
}

// TestAmbiguousWritesDetected: with ambiguous writes (outside the theorem's premise), the
// checker does catch the duplicate pod (issues/k8s-daemonset-ambiguous-create-duplicate-pod.md)
// in some runs; informational, it does not fail.
func TestAmbiguousWritesDetected(t *testing.T) {
	runs, checks := envInt("DSMAIN_AMBIGUOUS_RUNS", 20), envInt("DSMAIN_CHECKS", 2000)
	cfg := serverConfig()
	cfg.AmbiguousWrites = true
	caught := 0
	for i := 0; i < runs; i++ {
		func() {
			defer func() {
				if r := recover(); r != nil {
					caught++
					t.Logf("run %d: %v", i, r)
				}
			}()
			run(cfg, checks)
		}()
	}
	t.Logf("ambiguous writes: the checker panicked in %d of %d runs", caught, runs)
}
