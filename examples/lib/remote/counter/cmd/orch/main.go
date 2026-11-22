// Command orch is the counter instance's orchestrator machine (package counter).
package main

import "github.com/mit-pdos/etcd-grove/examples/lib/remote/counter"

func main() {
	counter.Orch([]string{counter.ClientAddr0, counter.ClientAddr1})
}
