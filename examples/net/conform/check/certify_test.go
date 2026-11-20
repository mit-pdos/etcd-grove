package check_test

import (
	"os"
	"os/exec"
	"path/filepath"
	"strings"
	"testing"
)

// TestCertify runs certify.py (README.md, "Certification in Lean"): the checker on the committed
// sample, the Lean replay of every witness against its run's calls (every run must be CERTIFIED),
// and the negative tests (tampered witnesses, each NOT CERTIFIED at the step it touched). It needs
// python3 and the replay, `lake build net-replay` at the repository's root: with
// NET_CERTIFY=1 it builds the replay itself (lake on the PATH), else it skips when the replay is
// not built.
func TestCertify(t *testing.T) {
	py, err := exec.LookPath("python3")
	if err != nil {
		t.Skip("python3 not found: the certification is not run")
	}
	root, err := filepath.Abs(filepath.Join("..", "..", "..", ".."))
	if err != nil {
		t.Fatal(err)
	}
	exe := filepath.Join(root, ".lake", "build", "bin", "net-replay")
	if os.Getenv("NET_CERTIFY") == "1" {
		lake, err := exec.LookPath("lake")
		if err != nil {
			t.Fatal("NET_CERTIFY=1 and no lake on the PATH")
		}
		cmd := exec.Command(lake, "build", "net-replay")
		cmd.Dir = root
		if out, err := cmd.CombinedOutput(); err != nil {
			t.Fatalf("lake build net-replay: %v\n%s", err, out)
		}
	}
	if _, err := os.Stat(exe); err != nil {
		t.Skipf("%s not built (lake build net-replay, or NET_CERTIFY=1): the certification is not run", exe)
	}
	cmd := exec.Command(py, "-B", "certify.py", "--exe", exe)
	cmd.Env = append(os.Environ(), "PYTHONDONTWRITEBYTECODE=1")
	out, err := cmd.CombinedOutput()
	if err != nil {
		t.Fatalf("python3 certify.py: %v\n%s", err, out)
	}
	lines := strings.Split(strings.TrimSpace(string(out)), "\n")
	t.Log(strings.Join(lines, "\n"))
}
