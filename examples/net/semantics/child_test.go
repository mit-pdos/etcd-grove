//go:build linux

package semantics

import (
	"bufio"
	"fmt"
	"io"
	"net"
	"os"
	"os/exec"
	"strings"
	"sync"
	"syscall"
	"testing"
	"time"
	"unsafe"
)

// Child processes: the test binary re-executed with NETSEM_CHILD set to a
// role (and NETSEM_ADDR to an address). A child reports on its stdout, one
// line per step; the parent waits for the line, then kills it with SIGKILL
// (or the child exits by itself: role suffix "-exit"). A child never exits
// on its own otherwise: it blocks until killed.

func TestMain(m *testing.M) {
	if role := os.Getenv("NETSEM_CHILD"); role != "" {
		runChild(role, os.Getenv("NETSEM_ADDR"))
		os.Exit(0)
	}
	os.Exit(m.Run())
}

func childFail(format string, args ...any) {
	fmt.Fprintf(os.Stderr, "child: "+format+"\n", args...)
	os.Exit(2)
}

func childInq(c *net.TCPConn) int {
	rc, _ := c.SyscallConn()
	var n int32
	rc.Control(func(fd uintptr) {
		syscall.Syscall(syscall.SYS_IOCTL, fd, siocInq, uintptr(unsafe.Pointer(&n)))
	})
	return int(n)
}

func runChild(role, addr string) {
	exit := strings.HasSuffix(role, "-exit")
	role = strings.TrimSuffix(role, "-exit")
	block := func() {
		if exit {
			os.Exit(0) // Go's runtime does not close sockets; the kernel does at exit
		}
		select {}
	}
	switch role {
	case "dial-write": // dial addr, write "hello", leave nothing unread
		c, err := net.Dial("tcp", addr)
		if err != nil {
			childFail("dial: %v", err)
		}
		if _, err := c.Write([]byte("hello")); err != nil {
			childFail("write: %v", err)
		}
		fmt.Println("ready")
		block()
	case "dial-write-unread": // dial addr, write "hello", wait until the parent's byte arrived, unread
		c, err := net.Dial("tcp", addr)
		if err != nil {
			childFail("dial: %v", err)
		}
		if _, err := c.Write([]byte("hello")); err != nil {
			childFail("write: %v", err)
		}
		end := time.Now().Add(waitLimit)
		for childInq(c.(*net.TCPConn)) == 0 {
			if time.Now().After(end) {
				childFail("parent's byte never arrived")
			}
			time.Sleep(time.Millisecond)
		}
		fmt.Println("ready")
		block()
	case "serve-read": // listen, print the address, accept one, read the 4-byte request, never reply
		ln, err := net.Listen("tcp", "127.0.0.1:0")
		if err != nil {
			childFail("listen: %v", err)
		}
		fmt.Println(ln.Addr().String())
		c, err := ln.Accept()
		if err != nil {
			childFail("accept: %v", err)
		}
		buf := make([]byte, 4)
		if _, err := io.ReadFull(c, buf); err != nil {
			childFail("read: %v", err)
		}
		fmt.Println("got")
		block()
	case "listen": // listen at addr (or :0 when empty), print the address, never accept
		if addr == "" {
			addr = "127.0.0.1:0"
		}
		ln, err := net.Listen("tcp", addr)
		if err != nil {
			childFail("listen: %v", err)
		}
		fmt.Println(ln.Addr().String())
		block()
	default:
		childFail("unknown role %q", role)
	}
}

// child is a running child process and its stdout.
type child struct {
	cmd *exec.Cmd
	out *bufio.Reader
}

// forkMu keeps forks out of the tests that need a Close to close its socket
// at once (they hold it for reading). A fork copies every fd of the test
// process into the child until the child's exec (CLOEXEC acts only at
// exec), so a listener closed meanwhile stays open in the kernel for a few
// milliseconds: measured, a Listen at its address then fails with
// EADDRINUSE, and a Dial to it completes the handshake and is then reset.
var forkMu sync.RWMutex

func startChild(t *testing.T, role, addr string) *child {
	t.Helper()
	cmd := exec.Command(os.Args[0], "-test.run=^$")
	cmd.Env = append(os.Environ(), "NETSEM_CHILD="+role, "NETSEM_ADDR="+addr)
	cmd.Stderr = os.Stderr
	out, err := cmd.StdoutPipe()
	if err != nil {
		t.Fatal(err)
	}
	forkMu.Lock()
	err = cmd.Start()
	forkMu.Unlock()
	if err != nil {
		t.Fatal(err)
	}
	ch := &child{cmd, bufio.NewReader(out)}
	t.Cleanup(func() { cmd.Process.Kill(); cmd.Wait() })
	return ch
}

// line waits (bounded) for the child's next line.
func (ch *child) line(t *testing.T) string {
	t.Helper()
	r := make(chan string, 1)
	go func() {
		s, _ := ch.out.ReadString('\n')
		r <- strings.TrimSpace(s)
	}()
	select {
	case s := <-r:
		if s == "" {
			t.Fatalf("child ended without output")
		}
		return s
	case <-time.After(waitLimit):
		t.Fatalf("child silent for %v", waitLimit)
	}
	return ""
}

// kill sends SIGKILL and waits until the process is reaped (its files, the
// sockets among them, are closed by then: do_exit closes them before the
// parent can reap it). A "-exit" child has exited by itself; kill then only
// reaps it.
func (ch *child) kill(t *testing.T) {
	t.Helper()
	ch.cmd.Process.Signal(syscall.SIGKILL)
	ch.cmd.Wait()
}
