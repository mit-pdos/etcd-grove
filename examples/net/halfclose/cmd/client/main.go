// Command client is halfclose's client node, a process of its own: it writes a request, shuts its write side, reads until EOF and checks.
// It runs over real TCP with the example's other nodes, each a process (the
// package's process tests); its main is the node's program in the example's
// distributed adequacy theorem.
package main

import "github.com/mit-pdos/etcd-grove/examples/net/halfclose"

func main() {
	halfclose.Call()
}
