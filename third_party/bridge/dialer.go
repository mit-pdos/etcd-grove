// The constructor this copy adds (UPSTREAM.md): etcd's integration framework builds a bridge
// with the unexported newBridge and its dialer type (tests/framework/integration/cluster.go:
// `dialer`, `Member.listenGRPC`); this file is that dialer, copied, and an exported New over it.

package bridge

import "net"

type dialer struct {
	network string
	addr    string
}

func (d dialer) Dial() (net.Conn, error) {
	return net.Dial(d.network, d.addr)
}

// New starts a bridge that accepts on l and forwards each connection to the TCP address addr,
// as etcd's integration framework does for a member's gRPC address (`UseBridge`).
func New(addr string, l net.Listener) Bridge {
	return newBridge(dialer{network: "tcp", addr: addr}, l)
}
