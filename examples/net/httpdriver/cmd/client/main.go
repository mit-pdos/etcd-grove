// Command client is httpdriver's client machine: it sends random requests and panics if a
// property net/http's server guarantees fails (package httpdriver).
package main

import "github.com/mit-pdos/etcd-grove/examples/net/httpdriver"

func main() {
	httpdriver.Client()
}
