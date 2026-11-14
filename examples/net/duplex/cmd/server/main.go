// Command server is duplex's server node, a process of its own: it echoes every read on each connection.
// It runs over real TCP with the example's other nodes, each a process (the
// package's process tests); its main is the node's program in the example's
// distributed adequacy theorem.
package main

import "github.com/mit-pdos/etcd-grove/examples/net/duplex"

func main() {
	duplex.Serve()
}
