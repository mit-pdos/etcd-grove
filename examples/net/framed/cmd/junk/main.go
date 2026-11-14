// Command junk is framed's junk node, a process of its own: it writes a header promising more bytes than it sends.
// It runs over real TCP with the example's other nodes, each a process (the
// package's process tests); its main is the node's program in the example's
// distributed adequacy theorem.
package main

import "github.com/mit-pdos/etcd-grove/examples/net/framed"

func main() {
	framed.SendJunk()
}
