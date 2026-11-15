// Package foreignconn is the evidence for the closed-world clause added to addrsUnclaimed
// (Proof/runtime/Start.lean), netAddrFree and netListenerAt (Proof/net/InvNet.lean) and
// net.Listen.wp_proof (Proof/net/Listen.lean) on 2026-11-14 (the network fault review; a world
// assumption the user accepted that day): binding is not all. A second process that binds
// nothing, so addrUnclaimed's clause on binds holds of it, dials the program's listener, and the
// program's Accept hands its connection over like one of the program's own clients'. So the
// premise now also says that no other process, nor unverified code of the program, connects to an
// address of As: the boundaries' facts (a handler gets the protocol's knowledge of every request,
// http.handlerOk; grpcServes) hold only of connections the program's verified code dialed.
package foreignconn

import (
	"bufio"
	"net"
	"os"
	"os/exec"
	"testing"
)

func TestForeignProcessConnects(t *testing.T) {
	if os.Getenv("FOREIGNCONN_CHILD") == "1" {
		c, err := net.Dial("tcp", os.Getenv("FOREIGNCONN_ADDR"))
		if err != nil {
			os.Exit(2)
		}
		c.Write([]byte("PUT k forged\n"))
		c.Close()
		os.Exit(0)
	}
	l, err := net.Listen("tcp", "127.0.0.1:0")
	if err != nil {
		t.Fatal(err)
	}
	defer l.Close()
	cmd := exec.Command(os.Args[0], "-test.run=^TestForeignProcessConnects$")
	cmd.Env = append(os.Environ(), "FOREIGNCONN_CHILD=1", "FOREIGNCONN_ADDR="+l.Addr().String())
	if err := cmd.Start(); err != nil {
		t.Fatal(err)
	}
	c, err := l.Accept()
	if err != nil {
		t.Fatal(err)
	}
	line, _ := bufio.NewReader(c).ReadString('\n')
	c.Close()
	if err := cmd.Wait(); err != nil {
		t.Fatalf("the other process: %v", err)
	}
	if line != "PUT k forged\n" {
		t.Fatalf("accepted %q", line)
	}
	t.Logf("accepted a connection of another process (pid %d): %q", cmd.Process.Pid, line)
}
