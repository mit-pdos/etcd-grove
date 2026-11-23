package client

import (
	"bufio"
	"io"
	"net"
	"net/http"
	"net/rpc"
	"sync/atomic"
	"testing"

	"github.com/imdea-software/swiftpaxos/dlog"
	"github.com/imdea-software/swiftpaxos/replica/defs"
)

// H1: dialMaster's handshake with the master (rpc over HTTP CONNECT) and its
// retry count. The behavior is the same before and after the change to
// rpc.DialHTTP: this test pins it (it passes on both sides).
func TestIssueH1_DialMasterHandshake(t *testing.T) {
	ml, err := net.Listen("tcp", "127.0.0.1:0")
	if err != nil {
		t.Fatal(err)
	}
	defer ml.Close()
	srv := rpc.NewServer()
	srv.RegisterName("Master", &fakeMaster{replicas: []string{"127.0.0.1:1"}})
	go http.Serve(ml, srv)

	c := NewClientLog("", "127.0.0.1", ml.Addr().(*net.TCPAddr).Port, true, false, false, &dlog.Logger{})
	m, err := c.dialMaster()
	if err != nil || m == nil || c.master != m {
		t.Fatalf("dialMaster: %v", err)
	}
	gl, err := c.callMaster("GetLeader")
	if err != nil || gl.(*defs.GetLeaderReply).LeaderId != 0 {
		t.Fatalf("GetLeader over the master connection: %v", err)
	}
	c.Disconnect()
}

func TestIssueH1_DialMasterWrongStatusRetries(t *testing.T) {
	l, err := net.Listen("tcp", "127.0.0.1:0")
	if err != nil {
		t.Fatal(err)
	}
	defer l.Close()
	var conns, connects atomic.Int32
	go func() {
		for {
			conn, err := l.Accept()
			if err != nil {
				return
			}
			conns.Add(1)
			go func(conn net.Conn) {
				defer conn.Close()
				line, err := bufio.NewReader(conn).ReadString('\n')
				if err != nil {
					return
				}
				if line == "CONNECT "+rpc.DefaultRPCPath+" HTTP/1.0\n" {
					connects.Add(1)
				}
				io.WriteString(conn, "HTTP/1.0 200 OK\n\n") // not rpc's status
				io.Copy(io.Discard, conn)
			}(conn)
		}
	}()

	c := NewClientLog("", "127.0.0.1", l.Addr().(*net.TCPAddr).Port, true, false, false, &dlog.Logger{})
	if m, err := c.dialMaster(); err == nil || m != nil {
		t.Fatalf("dialMaster succeeded against a server with a wrong status")
	}
	if n, k := conns.Load(), connects.Load(); n != 3 || k != 3 {
		t.Fatalf("dialMaster: %d connections, %d CONNECT requests; want 3 and 3", n, k)
	}
}
