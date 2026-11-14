// Command server is echo's server node, a process of its own: it listens at SrvAddr and echoes each connection's request.
// It runs over real TCP with the example's other nodes, each a process (the
// package's process tests); its main is the node's program in the example's
// distributed adequacy theorem.
package main

import "github.com/mit-pdos/etcd-grove/examples/net/echo"

func main() {
	echo.Serve()
}
