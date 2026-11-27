package durable

import (
	"path/filepath"
	"testing"
)

// TestReadWrite runs Read and Write as their callers do (in Go builds and under the Go-model overlay
// of examples/lib/durable.toml, whose model calls the stubs durableRead/durableWrite): a missing
// file reads as ("", false), a written one reads back, an overwrite replaces it.
func TestReadWrite(t *testing.T) {
	name := filepath.Join(t.TempDir(), "f")
	if s, ok := Read(name); s != "" || ok {
		t.Fatalf("Read of a missing file: %q, %v", s, ok)
	}
	Write(name, "one")
	if s, ok := Read(name); s != "one" || !ok {
		t.Fatalf("Read after Write: %q, %v", s, ok)
	}
	Write(name, "")
	if s, ok := Read(name); s != "" || !ok {
		t.Fatalf("Read after an empty Write: %q, %v", s, ok)
	}
}
