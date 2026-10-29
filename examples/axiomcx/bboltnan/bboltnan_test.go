package bboltnan

import (
	"path/filepath"
	"strings"
	"testing"
)

// TestRunPanics: Run panics in Commit (amd64: int(NaN) is MinInt64).
func TestRunPanics(t *testing.T) {
	defer func() {
		r := recover()
		if r == nil {
			t.Fatal("Run returned; expected a panic")
		}
		if s, ok := r.(string); !ok || !strings.HasPrefix(s, "inode overflow") {
			t.Fatalf("unexpected panic: %v", r)
		}
		t.Logf("Run panicked: %v", r)
	}()
	Run(filepath.Join(t.TempDir(), "db"))
}
