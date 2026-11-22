package robust

import (
	"bytes"
	"fmt"
	"os"
	"os/exec"
	"path/filepath"
	"strings"
)

// NewNetworkOrLocal makes a run's network: network namespaces (NewNetwork, tagged by prefix and
// this process's id) if netns, the local mode (LocalNetwork) otherwise.
func NewNetworkOrLocal(netns bool, prefix string) (*Network, error) {
	if !netns {
		return LocalNetwork(), nil
	}
	return NewNetwork(fmt.Sprintf("%s%d", prefix, os.Getpid()%100000))
}

// Symlink makes path a symbolic link to target, replacing what is there (and making path's
// directory).
func Symlink(target, path string) error {
	os.Remove(path)
	if err := os.MkdirAll(filepath.Dir(path), 0o755); err != nil {
		return err
	}
	return os.Symlink(target, path)
}

// TestLog is what RerunTest uses of a *testing.T (so that this package does not import testing).
type TestLog interface {
	Helper()
	Log(args ...any)
	Fatalf(format string, args ...any)
}

// rerunVar marks the test binary RerunTest started.
const rerunVar = "ROBUST_RERUN"

// RerunTest runs the test named name again where it can make network namespaces, if this process
// cannot (NetnsAvailable) and was not itself started by RerunTest: in a user namespace of its own if
// this process is root (a container's root without CAP_NET_ADMIN: RerunInUserns, the bridge
// variant), by sudo -n if it can (RerunAsRoot). The run gets the timeout timeout, -test.short if
// short, and the environment variables env added. Its output goes to t's log, and its failure fails
// t. It reports whether it ran the test: if not, the caller runs it here (in the local mode, one
// loopback address and no network faults, if namespaces are unavailable).
func RerunTest(t TestLog, name, timeout string, short bool, env []string) bool {
	t.Helper()
	if NetnsAvailable() == nil || os.Getenv(rerunVar) != "" {
		return false
	}
	args := []string{"-test.run=^" + name + "$", "-test.v", "-test.count=1", "-test.timeout=" + timeout}
	if short {
		args = append(args, "-test.short")
	}
	var rerun func([]string, []string, *bytes.Buffer) error
	if IsRoot() {
		rerun = func(a, e []string, out *bytes.Buffer) error { return RerunInUserns(a, e, out) }
	} else if exec.Command("sudo", "-n", "true").Run() == nil {
		rerun = func(a, e []string, out *bytes.Buffer) error { return RerunAsRoot(a, e, out) }
	}
	if rerun == nil {
		return false
	}
	var out bytes.Buffer
	err := rerun(args, append([]string{rerunVar + "=1"}, env...), &out)
	for _, l := range strings.Split(out.String(), "\n") {
		if strings.TrimSpace(l) != "" {
			t.Log(l)
		}
	}
	if err != nil {
		t.Fatalf("in the namespaces' child: %v", err)
	}
	return true
}
