// Command client0 is the counter instance's client machine 0 (package counter).
package main

import "github.com/mit-pdos/etcd-grove/examples/lib/remote/counter"

func main() {
	counter.Client(0, counter.ClientAddr0, counter.ServerAddr)
}
