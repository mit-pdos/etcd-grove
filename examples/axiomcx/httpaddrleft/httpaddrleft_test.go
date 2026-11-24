package httpaddrleft

import (
	"os"
	"os/exec"
	"strings"
	"testing"
)

// The panic is in the handler's goroutine, which no recover in the test reaches: the test runs Main
// in a child process and checks it dies with that panic.
func TestMainPanics(t *testing.T) {
	if os.Getenv("HTTPADDRLEFT_CHILD") == "1" {
		Main()
		return
	}
	cmd := exec.Command(os.Args[0], "-test.run=^TestMainPanics$")
	cmd.Env = append(os.Environ(), "HTTPADDRLEFT_CHILD=1")
	out, err := cmd.CombinedOutput()
	t.Logf("child: %v", err)
	if err == nil || !strings.Contains(string(out), "httpaddrleft: the handler got a request its address's protocol excludes") {
		t.Fatalf("Main did not panic as expected:\n%s", out)
	}
}
