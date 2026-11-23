package master

import (
	"net"
	"net/rpc"
	"os"
	"os/exec"
	"strconv"
	"testing"
	"time"

	"github.com/imdea-software/swiftpaxos-epaxos/config"
	"github.com/imdea-software/swiftpaxos-epaxos/dlog"
)

// TestRunRegisterError [M-REG]: if rpc.Register fails for the master (here: a "Master" service
// is already registered in the default server), Run must not serve: it would serve with no
// Master service of its own, so every replica's registration would fail forever. Before the
// fix Run ignores the error and serves (never returns); after it, Run returns. Run in a child
// process: rpc.HandleHTTP may be called once per process.
func TestRunRegisterError(t *testing.T) {
	if os.Getenv("MREG_CHILD") != "" {
		port, _ := strconv.Atoi(os.Getenv("MREG_CHILD"))
		other := New(5, port, &config.Config{Proxy: &config.ProxyInfo{}}, &dlog.Logger{})
		if err := rpc.Register(other); err != nil {
			os.Exit(3)
		}
		m := New(5, port, &config.Config{Proxy: &config.ProxyInfo{}}, &dlog.Logger{})
		m.Run()
		os.Exit(0) // Run returned
	}
	l, err := net.Listen("tcp", "127.0.0.1:0")
	if err != nil {
		t.Fatal(err)
	}
	port := l.Addr().(*net.TCPAddr).Port
	l.Close()
	cmd := exec.Command(os.Args[0], "-test.run=TestRunRegisterError")
	cmd.Env = append(os.Environ(), "MREG_CHILD="+strconv.Itoa(port))
	if err := cmd.Start(); err != nil {
		t.Fatal(err)
	}
	done := make(chan error, 1)
	go func() { done <- cmd.Wait() }()
	select {
	case err := <-done:
		if err != nil {
			t.Fatalf("child: %v", err)
		}
	case <-time.After(5 * time.Second):
		cmd.Process.Kill()
		t.Fatal("Run kept serving after rpc.Register failed")
	}
}
