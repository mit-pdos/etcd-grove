// Command server is rpcdriver's server machine: it serves the driver's service over raw TCP and
// over HTTP (package rpcdriver).
package main

import "github.com/mit-pdos/etcd-grove/examples/net/rpcdriver"

func main() {
	rpcdriver.Register() // net/rpc's codec (rpcgen's; nothing in a real build)
	rpcdriver.Server()
}
