// Command client is duplex's client node, a process of its own: it writes 1..4 from one goroutine and checks them in another.
// It runs over real TCP with the example's other nodes, each a process (the
// package's process tests); its main is the node's program in the example's
// distributed adequacy theorem.
package main

import "github.com/mit-pdos/etcd-grove/examples/net/duplex"

func main() {
	duplex.Call()
}
