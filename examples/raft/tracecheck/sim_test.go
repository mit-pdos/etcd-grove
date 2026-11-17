//go:build with_tla

package tracecheck

import (
	"bytes"
	"os"
	"path/filepath"
	"strconv"
	"testing"
)

// TestRunTraces runs a few seeds: the cluster elects a leader and commits proposals, and the
// trace is written. With TRACE_DIR set, each trace goes to $TRACE_DIR/seed-<n>.ndjson (for
// upstream's tla/validate.sh).
func TestRunTraces(t *testing.T) {
	dir := os.Getenv("TRACE_DIR")
	seeds := 5
	if n, err := strconv.Atoi(os.Getenv("TRACE_SEEDS")); err == nil && n > 0 {
		seeds = n
	}
	for seed := uint64(1); seed <= uint64(seeds); seed++ {
		s, err := New(DefaultConfig(seed))
		if err != nil {
			t.Fatal(err)
		}
		if err := s.Run(); err != nil {
			t.Fatalf("seed %d: %v", seed, err)
		}
		var buf bytes.Buffer
		if err := WriteNDJSON(&buf, s.Events()); err != nil {
			t.Fatal(err)
		}
		t.Logf("seed %d: %d events, leaders %v, max commit %d, proposed %d, delivered %d, dropped %d, readies %d",
			seed, len(s.Events()), s.Leaders(), s.MaxCommit(), s.Proposed, s.Delivered, s.Dropped, s.Readies)
		if s.MaxCommit() <= 3 {
			t.Errorf("seed %d: nothing committed beyond the bootstrap entries", seed)
		}
		if dir != "" {
			if err := os.WriteFile(filepath.Join(dir, "seed-"+strconv.FormatUint(seed, 10)+".ndjson"), buf.Bytes(), 0o644); err != nil {
				t.Fatal(err)
			}
		}
	}
}
