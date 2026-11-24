package grpcdriver

import (
	"bytes"
	"net"
	"os"
	"os/exec"
	"sync"
	"testing"
	"time"
)

// Run with the real grpc-go (go test) and with its model (models/grpc/gomodel.py).

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

// startServer runs the server in this process, once (as a machine), and waits until both addresses accept.
func startServer(t *testing.T) {
	serverOnce.Do(func() {
		go Server()
	})
	waitListen(t, Addr)
}

// waitListen waits until something accepts connections at a.
func waitListen(t *testing.T, a string) {
	{
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

// TestMain runs this test binary as a machine when GRPCDRIVER_NODE says which ("server" or
// "client"): the machines' programs (cmd/server, cmd/client), built with the test's tags (the
// real grpc-go, or its model through the module replacement of models/grpc/gomodel.py).
func TestMain(m *testing.M) {
	switch os.Getenv("GRPCDRIVER_NODE") {
	case "server":
		Server()
		os.Exit(0)
	case "client":
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
	cmd.Env = append(os.Environ(), "GRPCDRIVER_NODE="+id)
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
	waitListen(t, Addr)
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
	for _, s := range []string{"unary-reply", "status-roundtrip", "metadata", "ctx-canceled", "server-stream", "client-stream", "bidi-stream", "error-set", "concurrent-calls", "close"} {
		if counts.m[s] == 0 {
			t.Errorf("section %s: its check was never reached", s)
		}
	}
	t.Logf("checks reached: %v", counts.m)
}
