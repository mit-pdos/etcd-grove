package main

import (
	"bufio"
	"io"
	"net"
	"os"
	"os/exec"
	"path/filepath"
	"sync"
	"testing"
	"time"
)

// TestTwoNodes builds this command (in the mode of the test's own build: real modules, or the
// models with go.model.mod and the tag rpcmodel; EXAMPLE_GOFLAGS) and runs a server node and a
// client node as separate processes on loopback, then again with a proxy between them that cuts
// every connection every 30 ms (the client reconnects; failed calls are allowed, wrong replies
// are not).
func TestTwoNodes(t *testing.T) {
	bin := filepath.Join(t.TempDir(), "example")
	args := []string{"build", "-o", bin}
	if model {
		args = append(args, "-modfile=../go.model.mod", "-tags", "rpcmodel")
	}
	b := exec.Command("go", append(args, ".")...)
	b.Stderr = os.Stderr
	if err := b.Run(); err != nil {
		t.Fatal(err)
	}
	for _, faults := range []bool{false, true} {
		addr := freeAddr(t)
		srv := exec.Command(bin, "server", addr)
		out, _ := srv.StdoutPipe()
		srv.Stderr = os.Stderr
		if err := srv.Start(); err != nil {
			t.Fatal(err)
		}
		if l, _ := bufio.NewReader(out).ReadString('\n'); l != "serving\n" {
			t.Fatalf("server: %q", l)
		}
		target := addr
		var stop func()
		if faults {
			target, stop = cutter(t, addr)
		}
		cl := exec.Command(bin, "client", target, "200")
		cl.Stderr = os.Stderr
		o, err := cl.Output()
		t.Logf("faults=%v: %s", faults, o)
		if stop != nil {
			stop()
		}
		srv.Process.Kill()
		srv.Wait()
		if err != nil {
			t.Fatalf("client: %v", err)
		}
	}
}

func freeAddr(t *testing.T) string {
	l, err := net.Listen("tcp", "127.0.0.1:0")
	if err != nil {
		t.Fatal(err)
	}
	defer l.Close()
	return l.Addr().String()
}

// cutter is a proxy to target that closes every connection every 30 ms.
func cutter(t *testing.T, target string) (string, func()) {
	l, err := net.Listen("tcp", "127.0.0.1:0")
	if err != nil {
		t.Fatal(err)
	}
	var mu sync.Mutex
	var conns []net.Conn
	done := make(chan struct{})
	go func() {
		for {
			c, err := l.Accept()
			if err != nil {
				return
			}
			s, err := net.Dial("tcp", target)
			if err != nil {
				c.Close()
				continue
			}
			mu.Lock()
			conns = append(conns, c, s)
			mu.Unlock()
			go func() { io.Copy(s, c); s.Close() }()
			go func() { io.Copy(c, s); c.Close() }()
		}
	}()
	go func() {
		for {
			select {
			case <-done:
				return
			case <-time.After(30 * time.Millisecond):
			}
			mu.Lock()
			for _, c := range conns {
				c.Close()
			}
			conns = nil
			mu.Unlock()
		}
	}()
	return l.Addr().String(), func() { close(done); l.Close() }
}
