// Command server is acceptloop's server node, a process of its own: it accepts connections, one goroutine each.
// It runs over real TCP with the example's other nodes, each a process (the
// package's process tests); its main is the node's program in the example's
// distributed adequacy theorem.
package main

import "github.com/mit-pdos/etcd-grove/examples/net/acceptloop"

func main() {
	acceptloop.Serve()
}
