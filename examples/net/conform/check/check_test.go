// Package check_test runs the conformance checker's tests (test_check.py: the model, the lazy
// search against a brute-force one, hand-made traces, the committed sample and its mutants), so
// that `go test ./net/...` covers the checker, which is Python (README.md). It skips when no
// python3 is on the PATH.
package check_test

import (
	"os"
	"os/exec"
	"strings"
	"testing"
)

func TestChecker(t *testing.T) {
	py, err := exec.LookPath("python3")
	if err != nil {
		t.Skip("python3 not found: the checker's tests are not run")
	}
	cmd := exec.Command(py, "-B", "test_check.py")
	cmd.Env = append(os.Environ(), "PYTHONDONTWRITEBYTECODE=1")
	out, err := cmd.CombinedOutput()
	if err != nil {
		t.Fatalf("python3 test_check.py: %v\n%s", err, out)
	}
	lines := strings.Split(strings.TrimSpace(string(out)), "\n")
	if len(lines) > 3 {
		lines = lines[len(lines)-3:]
	}
	t.Log(strings.Join(lines, "\n"))
}
