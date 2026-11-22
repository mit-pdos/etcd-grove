// Command server is the counter instance's server machine (package counter).
package main

import "github.com/mit-pdos/etcd-grove/examples/lib/remote/counter"

func main() {
	counter.Server(counter.ServerAddr)
}
