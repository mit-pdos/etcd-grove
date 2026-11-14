// Command server is preface's server node, a process of its own: it reads a preface under a deadline, then echoes a byte.
// It runs over real TCP with the example's other nodes, each a process (the
// package's process tests); its main is the node's program in the example's
// distributed adequacy theorem.
package main

import "github.com/mit-pdos/etcd-grove/examples/net/preface"

func main() {
	preface.Serve()
}
