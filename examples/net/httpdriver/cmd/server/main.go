// Command server is httpdriver's server machine: it serves the driver's ServeMux (package httpdriver).
package main

import "github.com/mit-pdos/etcd-grove/examples/net/httpdriver"

func main() {
	httpdriver.Server()
}
