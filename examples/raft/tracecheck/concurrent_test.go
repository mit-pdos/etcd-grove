//go:build with_tla

package tracecheck

import (
	"bytes"
	"os"
	"path/filepath"
	"strconv"
	"testing"

	"github.com/anishathalye/porcupine"
)

// concurrentNDJSON runs a concurrent cluster and returns its trace as NDJSON.
func concurrentNDJSON(t *testing.T, cfg CConfig) ([]byte, *Cluster) {
	c, err := RunConcurrent(cfg)
	if err != nil {
		t.Fatal(err)
	}
	var buf bytes.Buffer
	if err := WriteNDJSON(&buf, c.Events()); err != nil {
		t.Fatal(err)
	}
	return buf.Bytes(), c
}

// TestConcurrentTraces: the traces of concurrent runs (DefaultCConfig, seeds 1..TRACE_SEEDS,
// default 10) are matched, by the direct checker and by porcupine. With TRACE_DIR set, each goes
// to $TRACE_DIR/conc-<n>.ndjson.
func TestConcurrentTraces(t *testing.T) {
	dir := os.Getenv("TRACE_DIR")
	for seed := uint64(1); seed <= uint64(envInt("TRACE_SEEDS", 10)); seed++ {
		nd, c := concurrentNDJSON(t, DefaultCConfig())
		if dir != "" {
			if err := os.WriteFile(filepath.Join(dir, "conc-"+strconv.FormatUint(seed, 10)+".ndjson"), nd, 0o644); err != nil {
				t.Fatal(err)
			}
		}
		r, pc, err := goVerdicts(t, nd)
		t.Logf("seed %d: %d events, proposed %d, delivered %d, dropped %d, readies %d: direct %v, porcupine %v",
			seed, len(c.Events()), c.Proposed.Load(), c.Delivered.Load(), c.Dropped.Load(), c.Readies.Load(), r, pc)
		if err != nil || !r.TLCOK() || pc != porcupine.Ok {
			t.Errorf("seed %d: direct %v (err %v), porcupine %v", seed, r, err, pc)
		}
	}
}
