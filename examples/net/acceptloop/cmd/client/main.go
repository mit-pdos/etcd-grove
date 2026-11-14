// Command client is acceptloop's client node, a process of its own: it makes two concurrent calls and checks each reply.
// It runs over real TCP with the example's other nodes, each a process (the
// package's process tests); its main is the node's program in the example's
// distributed adequacy theorem.
package main

import "github.com/mit-pdos/etcd-grove/examples/net/acceptloop"

func main() {
	acceptloop.Call()
}
