package proctest

import (
	"bytes"
	"fmt"
	"os"
	"os/exec"
	"path/filepath"
	"strings"
	"sync"
	"testing"

	"github.com/mit-pdos/etcd-grove/examples/net/conform/events"
	"github.com/mit-pdos/etcd-grove/examples/net/conform/overlay"
)

// Conformance tracing (examples/net/conform/README.md): only with NETTCP_CONFORM=1.
var conformOn = os.Getenv("NETTCP_CONFORM") == "1"

var conform struct {
	mu      sync.Mutex
	overlay string                 // the overlay file
	root    string                 // the trace root
	dirs    map[*testing.T]string  // a test's trace directory
	bins    map[string]string      // a built binary's trace directory
	logs    map[string]*events.Log // a trace directory's driver file
}

// conformOverlay is the tracer's overlay file: $NETTCP_OVERLAY if set (the collection makes it
// once), else one made for this test process.
func conformOverlay(t *testing.T) string {
	t.Helper()
	conform.mu.Lock()
	defer conform.mu.Unlock()
	if conform.overlay != "" {
		return conform.overlay
	}
	if p := os.Getenv("NETTCP_OVERLAY"); p != "" {
		conform.overlay = p
		return p
	}
	dir, err := os.MkdirTemp("", "nettcp-overlay-")
	if err != nil {
		t.Fatal(err)
	}
	p, err := overlay.Make(dir)
	if err != nil {
		t.Fatal(err)
	}
	conform.overlay = p
	return p
}

func sanitize(s string) string {
	return strings.Map(func(r rune) rune {
		if r >= 'a' && r <= 'z' || r >= 'A' && r <= 'Z' || r >= '0' && r <= '9' || r == '.' || r == '-' || r == '_' {
			return r
		}
		return '_'
	}, s)
}

// conformBuilt gives the binary bin, built by test t, t's trace directory
// (<root>/<package>/<test>, a fresh one per test run) and opens its driver file.
func conformBuilt(t *testing.T, bin string) {
	t.Helper()
	conform.mu.Lock()
	defer conform.mu.Unlock()
	if conform.dirs == nil {
		conform.dirs = map[*testing.T]string{}
		conform.bins = map[string]string{}
		conform.logs = map[string]*events.Log{}
	}
	dir, ok := conform.dirs[t]
	if !ok {
		if conform.root == "" {
			conform.root = os.Getenv("NETTCP_TRACE_DIR")
			if conform.root == "" {
				r, err := os.MkdirTemp("", "nettcp-trace-")
				if err != nil {
					t.Fatal(err)
				}
				conform.root = r
			}
		}
		wd, _ := os.Getwd()
		base := filepath.Join(conform.root, sanitize(filepath.Base(wd)), sanitize(t.Name()))
		if err := os.MkdirAll(filepath.Dir(base), 0o755); err != nil {
			t.Fatal(err)
		}
		dir = base
		for i := 2; ; i++ {
			err := os.Mkdir(dir, 0o755)
			if err == nil {
				break
			}
			if !os.IsExist(err) {
				t.Fatal(err)
			}
			dir = fmt.Sprintf("%s.%d", base, i)
		}
		log, err := events.Open(dir, "proctest")
		if err != nil {
			t.Fatal(err)
		}
		conform.dirs[t] = dir
		conform.logs[dir] = log
		t.Logf("conformance traces: %s", dir)
	}
	conform.bins[bin] = dir
}

// conformEnv sets cmd's environment for the node bin and returns its trace directory's driver
// file.
func conformEnv(cmd *exec.Cmd, bin string) *events.Log {
	conform.mu.Lock()
	dir := conform.bins[bin]
	log := conform.logs[dir]
	conform.mu.Unlock()
	if dir == "" {
		panic("proctest: conformance tracing: " + bin + " was not built by Build")
	}
	cmd.Env = append(os.Environ(), "NETTCP_NODE="+filepath.Base(bin), "NETTCP_TRACE_DIR="+dir)
	return log
}

// conformKill records the kill of p, unless it has already ended.
func conformKill(p *Proc) {
	select {
	case <-p.done:
		return
	default:
	}
	p.log.Kill(filepath.Base(p.cmd.Path), p.cmd.Process.Pid)
}

// conformRun is Run's body (CombinedOutput) with the node's environment and its events.
func conformRun(cmd *exec.Cmd, bin string) error {
	log := conformEnv(cmd, bin)
	var out bytes.Buffer
	cmd.Stdout = &out
	cmd.Stderr = &out
	err := cmd.Start()
	if err == nil {
		log.Start(filepath.Base(bin), cmd.Process, bin)
		err = cmd.Wait()
		log.Exit(filepath.Base(bin), cmd.Process.Pid, cmd.ProcessState)
	}
	if err != nil {
		return fmt.Errorf("%s: %v\n%s", filepath.Base(bin), err, out.Bytes())
	}
	return nil
}
