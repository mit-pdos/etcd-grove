// Package proctest runs an example's nodes as separate processes that talk over
// real TCP, for the examples' process tests: each node is a command of the
// example (cmd/server, cmd/client, ...), built and run as its own process, so
// the test runs the same programs, as the same separate processes, as the
// example's distributed adequacy theorem speaks of (examples/net/README.md).
//
// A test never connects to the nodes itself (the theorems assume a closed world:
// nothing outside the system uses its addresses); it waits for a listener by
// reading the kernel's socket table, /proc/net/tcp.
//
// With NETTCP_CONFORM=1 (conformance tracing, examples/net/conform/README.md), Build
// builds each command with the tracer's overlay of Go's net package, and Start and Run give
// each node's process NETTCP_NODE (the command's name) and NETTCP_TRACE_DIR (the test's
// trace directory, $NETTCP_TRACE_DIR/<package>/<test>, or under a temporary directory), and
// record its start, kill and exit in the directory's driver file (conform/events). Nothing
// changes otherwise.
package proctest

import (
	"bytes"
	"context"
	"encoding/hex"
	"fmt"
	"net"
	"os"
	"os/exec"
	"path/filepath"
	"strconv"
	"strings"
	"sync"
	"testing"
	"time"

	"github.com/mit-pdos/etcd-grove/examples/net/conform/events"
)

// Build builds the commands cmds (package paths, relative to the test's
// directory: "./cmd/server") into a temporary directory and returns each
// binary's path by the command's last path element ("server").
func Build(t *testing.T, cmds ...string) map[string]string {
	t.Helper()
	dir := t.TempDir()
	bins := map[string]string{}
	for _, c := range cmds {
		name := filepath.Base(c)
		out := filepath.Join(dir, name)
		args := []string{"build", "-o", out, c}
		if conformOn {
			args = []string{"build", "-overlay", conformOverlay(t), "-o", out, c}
		}
		b, err := exec.Command("go", args...).CombinedOutput()
		if err != nil {
			t.Fatalf("go build %s: %v\n%s", c, err, b)
		}
		bins[name] = out
		if conformOn {
			conformBuilt(t, out)
		}
	}
	return bins
}

// Proc is a node's running process.
type Proc struct {
	cmd  *exec.Cmd
	mu   sync.Mutex
	out  bytes.Buffer
	done chan struct{}
	err  error
	log  *events.Log // conformance tracing: the trace directory's driver file
}

type lockedWriter struct{ p *Proc }

func (w lockedWriter) Write(b []byte) (int, error) {
	w.p.mu.Lock()
	defer w.p.mu.Unlock()
	return w.p.out.Write(b)
}

// Start starts bin as a node's process; the test's cleanup kills it.
func Start(t *testing.T, bin string) *Proc {
	t.Helper()
	p := &Proc{done: make(chan struct{})}
	p.cmd = exec.Command(bin)
	p.cmd.Stdout = lockedWriter{p}
	p.cmd.Stderr = lockedWriter{p}
	if conformOn {
		p.log = conformEnv(p.cmd, bin)
	}
	if err := p.cmd.Start(); err != nil {
		t.Fatalf("start %s: %v", bin, err)
	}
	if conformOn {
		p.log.Start(filepath.Base(bin), p.cmd.Process, bin)
	}
	go func() {
		p.err = p.cmd.Wait()
		if conformOn {
			p.log.Exit(filepath.Base(bin), p.cmd.Process.Pid, p.cmd.ProcessState)
		}
		close(p.done)
	}()
	t.Cleanup(p.Kill)
	return p
}

// Kill kills the process with SIGKILL (a crash: its kernel closes its sockets)
// and waits for it.
func (p *Proc) Kill() {
	if conformOn {
		conformKill(p)
	}
	_ = p.cmd.Process.Kill()
	<-p.done
}

// Alive fails the test if the process has exited (a node that runs until it is
// killed, as a server).
func (p *Proc) Alive(t *testing.T) {
	t.Helper()
	select {
	case <-p.done:
		p.mu.Lock()
		defer p.mu.Unlock()
		t.Fatalf("node exited: %v\n%s", p.err, p.out.String())
	default:
	}
}

// Run runs bin to completion: an error unless it exits 0 within timeout (a
// panic exits 2, its message on stderr).
func Run(bin string, timeout time.Duration) error {
	ctx, cancel := context.WithTimeout(context.Background(), timeout)
	defer cancel()
	if conformOn {
		return conformRun(exec.CommandContext(ctx, bin), bin)
	}
	out, err := exec.CommandContext(ctx, bin).CombinedOutput()
	if err != nil {
		return fmt.Errorf("%s: %v\n%s", filepath.Base(bin), err, out)
	}
	return nil
}

// RunOK is Run, failing the test on an error.
func RunOK(t *testing.T, bin string, timeout time.Duration) {
	t.Helper()
	if err := Run(bin, timeout); err != nil {
		t.Fatal(err)
	}
}

// WaitListen waits until a socket listens at addr (an IPv4 "IP:port"), read from
// /proc/net/tcp.
func WaitListen(t *testing.T, addr string) {
	t.Helper()
	want, err := procAddr(addr)
	if err != nil {
		t.Fatal(err)
	}
	deadline := time.Now().Add(10 * time.Second)
	for {
		if listening(want) {
			return
		}
		if time.Now().After(deadline) {
			t.Fatalf("nothing listens at %s", addr)
		}
		time.Sleep(5 * time.Millisecond)
	}
}

// procAddr is addr as /proc/net/tcp writes a local address: the IPv4 address's
// four bytes in hex, least significant first, and the port in hex.
func procAddr(addr string) (string, error) {
	host, port, err := net.SplitHostPort(addr)
	if err != nil {
		return "", err
	}
	ip := net.ParseIP(host).To4()
	if ip == nil {
		return "", fmt.Errorf("not an IPv4 address: %s", addr)
	}
	p, err := strconv.Atoi(port)
	if err != nil {
		return "", err
	}
	rev := []byte{ip[3], ip[2], ip[1], ip[0]}
	return strings.ToUpper(hex.EncodeToString(rev)) + fmt.Sprintf(":%04X", p), nil
}

func listening(local string) bool {
	b, err := os.ReadFile("/proc/net/tcp")
	if err != nil {
		return false
	}
	for _, line := range strings.Split(string(b), "\n")[1:] {
		f := strings.Fields(line)
		if len(f) > 3 && f[1] == local && f[3] == "0A" {
			return true
		}
	}
	return false
}
