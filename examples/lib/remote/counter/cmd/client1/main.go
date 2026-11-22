// Command client1 is the counter instance's client machine 1 (package counter).
package main

import "github.com/mit-pdos/etcd-grove/examples/lib/remote/counter"

func main() {
	counter.Client(1, counter.ClientAddr1, counter.ServerAddr)
}
