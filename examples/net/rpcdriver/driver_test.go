package rpcdriver

import (
	"bytes"
	"net"
	"os"
	"os/exec"
	"sync"
	"testing"
	"time"

	"github.com/mit-pdos/etcd-grove/examples/net/internal/proctest"
)

// Run with the real net/rpc and net/http (go test) and with the models (a GOROOT of
// models/goroot.py's farm, -tags netmodel), as the kits' tests are.

// counts counts the sections' checks reached (the driver's reached hook).
var counts = struct {
	sync.Mutex
	m map[string]int
}{m: map[string]int{}}

func count(section string) {
	counts.Lock()
	counts.m[section]++
	counts.Unlock()
}

var serverOnce sync.Once

// startServer runs the server in this process, once (net/rpc's DefaultServer and net/http's
// DefaultServeMux are per process), and waits until both addresses accept.
func startServer(t *testing.T) {
	serverOnce.Do(func() {
		Register() // the codec, once in this process
		go Server()
	})
	for _, a := range []string{TCPAddr, HTTPAddr} {
		deadline := time.Now().Add(10 * time.Second)
		for {
			c, err := net.Dial("tcp", a)
			if err == nil {
				c.Close()
				break
			}
			if time.Now().After(deadline) {
				t.Fatalf("the server does not listen at %s", a)
			}
			time.Sleep(10 * time.Millisecond)
		}
	}
}

// TestMain runs this test binary as a machine when RPCDRIVER_NODE says which ("server" or
// "client"): the machines' programs (cmd/server, cmd/client), built with the test's tags (the
// real libraries, or the models with -tags netmodel).
func TestMain(m *testing.M) {
	switch os.Getenv("RPCDRIVER_NODE") {
	case "server":
		Register()
		Server()
		os.Exit(0)
	case "client":
		Register()
		Client()
		os.Exit(0)
	}
	os.Exit(m.Run())
}

// node runs this test binary as the machine id (TestMain).
func node(t *testing.T, id string) *exec.Cmd {
	exe, err := os.Executable()
	if err != nil {
		t.Fatal(err)
	}
	cmd := exec.Command(exe, "-test.run=^$")
	cmd.Env = append(os.Environ(), "RPCDRIVER_NODE="+id)
	return cmd
}

// TestProcesses (first: TestNonVacuity then holds the addresses in this process) runs the server
// machine and, against it, the client machine again and again, each a process over real TCP:
// every client run exits 0 (none panics), and the server is still running.
func TestProcesses(t *testing.T) {
	srv := node(t, "server")
	var srvOut bytes.Buffer
	srv.Stdout, srv.Stderr = &srvOut, &srvOut
	if err := srv.Start(); err != nil {
		t.Fatal(err)
	}
	done := make(chan error, 1)
	go func() { done <- srv.Wait() }()
	defer func() {
		srv.Process.Kill()
		<-done // the addresses are free again for TestNonVacuity
	}()
	proctest.WaitListen(t, TCPAddr)
	proctest.WaitListen(t, HTTPAddr)
	for i := 0; i < 20; i++ {
		if out, err := node(t, "client").CombinedOutput(); err != nil {
			t.Fatalf("client run %d: %v\n%s", i, err, out)
		}
	}
	select {
	case err := <-done:
		done <- err
		t.Fatalf("the server exited: %v\n%s", err, srvOut.String())
	default:
	}
}

// TestNonVacuity runs the client many times against the server, in this process: no run panics,
// and every section's property is checked on some run (its check reached, not skipped by an
// error), the success path of each kind of call included.
func TestNonVacuity(t *testing.T) {
	reached = count
	defer func() { reached = func(string) {} }()
	startServer(t)
	for i := 0; i < 200; i++ {
		Client()
	}
	for _, s := range []string{"register", "call-success", "server-error", "concurrent-calls", "close"} {
		if counts.m[s] == 0 {
			t.Errorf("section %s: its check was never reached", s)
		}
	}
	t.Logf("checks reached: %v", counts.m)
}
