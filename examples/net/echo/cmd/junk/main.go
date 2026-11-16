// Command junk is echo's junk node, a process of its own: it dials the server and writes bytes of its own.
// It runs over real TCP with the example's other nodes, each a process (the
// package's process tests); its main is the node's program in the example's
// distributed adequacy theorem.
package main

import "github.com/mit-pdos/etcd-grove/examples/net/echo"

func main() {
	echo.SendJunk()
}
