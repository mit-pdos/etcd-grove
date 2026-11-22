package robust

import (
	"bytes"
	"fmt"
	"net"
	"os"
	"os/exec"
	"path/filepath"
	"strings"
	"sync"
	"time"
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

// How many times, and how far apart, AwaitAccept tries to connect to an address.
const (
	acceptTries = 300
	acceptPause = 100 * time.Millisecond
)

// AwaitAccept waits until every address accepts a TCP connection (a liveness wait: a connection
// that carries no request runs nothing), trying each for 30 seconds, and reports whether all did.
func AwaitAccept(addrs []string) bool {
	for _, a := range addrs {
		up := false
		for t := 0; t < acceptTries && !up; t++ {
			c, err := net.DialTimeout("tcp", a, time.Second)
			if err == nil {
				c.Close()
				up = true
			} else {
				time.Sleep(acceptPause)
			}
		}
		if !up {
			return false
		}
	}
	return true
}

// Rotate is xs from its i-th (mod len) element on: the clients of a workload made of the same
// endpoints prefer different members (a client's balancer picks among the endpoints, the first
// first).
func Rotate[T any](xs []T, i int) []T {
	k := len(xs)
	out := make([]T, k)
	for j := 0; j < k; j++ {
		out[j] = xs[(i+j)%k]
	}
	return out
}

// CallAll runs call at every address addrs[c] with the input ins[c], all at once, and returns
// their outputs and whether each answered.
func CallAll[I, O any](addrs []string, ins []I, call func(addr string, in I) (O, bool)) ([]O, []bool) {
	outs := make([]O, len(addrs))
	oks := make([]bool, len(addrs))
	var wg sync.WaitGroup
	for c := range addrs {
		wg.Add(1)
		go func() {
			outs[c], oks[c] = call(addrs[c], ins[c])
			wg.Done()
		}()
	}
	wg.Wait()
	return outs, oks
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
