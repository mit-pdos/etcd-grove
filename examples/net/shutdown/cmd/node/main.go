// Command node is shutdown's node node, a process of its own: it listens, dials itself, then closes everything and checks that each later operation fails.
// It runs over real TCP with the example's other nodes, each a process (the
// package's process tests); its main is the node's program in the example's
// distributed adequacy theorem.
package main

import "github.com/mit-pdos/etcd-grove/examples/net/shutdown"

func main() {
	shutdown.Run()
}
