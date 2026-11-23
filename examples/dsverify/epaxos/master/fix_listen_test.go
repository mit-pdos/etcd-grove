package master

import (
	"net"
	"testing"

	"github.com/imdea-software/swiftpaxos-epaxos/config"
	"github.com/imdea-software/swiftpaxos-epaxos/dlog"
)

// TestRunListenError: the master's port is in use, so Run's Listen fails. With the
// non-verbose logger master.Fatal does not exit; Run must stop (return) instead of serving
// on a nil listener (a nil-interface call in http.Serve).
func TestRunListenError(t *testing.T) {
	occupied, err := net.Listen("tcp", ":0")
	if err != nil {
		t.Fatal(err)
	}
	defer occupied.Close()
	port := occupied.Addr().(*net.TCPAddr).Port
	m := New(5, port, &config.Config{Proxy: &config.ProxyInfo{}}, &dlog.Logger{})
	m.Run() // returns
}
