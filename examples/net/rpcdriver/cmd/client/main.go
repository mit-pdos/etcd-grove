// Command client is rpcdriver's client machine: it makes random calls and panics if a property
// net/rpc guarantees fails (package rpcdriver).
package main

import "github.com/mit-pdos/etcd-grove/examples/net/rpcdriver"

func main() {
	rpcdriver.Register() // net/rpc's codec (rpcgen's; nothing in a real build)
	rpcdriver.Client()
}
