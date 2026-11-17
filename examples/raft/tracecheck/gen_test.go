//go:build with_tla

package tracecheck

import (
	"bytes"
	"os"
	"path/filepath"
	"strconv"
	"testing"
)

// TestGenFull writes FullConfig traces of seeds 1..TRACE_SEEDS to $TRACE_DIR/full-<n>.ndjson
// (skipped without TRACE_DIR).
func TestGenFull(t *testing.T) {
	dir := os.Getenv("TRACE_DIR")
	if dir == "" {
		t.Skip("TRACE_DIR not set")
	}
	for seed := uint64(1); seed <= uint64(envInt("TRACE_SEEDS", 5)); seed++ {
		s, err := New(FullConfig(seed))
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
		t.Logf("seed %d: %d events, commit %d, conf changes %d, snapshots %d, restarts %d", seed, len(s.Events()),
			s.MaxCommit(), s.ConfChanges, s.Snapshots, s.Restarts)
		if err := os.WriteFile(filepath.Join(dir, "full-"+strconv.FormatUint(seed, 10)+".ndjson"), buf.Bytes(), 0o644); err != nil {
			t.Fatal(err)
		}
	}
}
