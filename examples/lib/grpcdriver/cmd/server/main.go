// Command server is grpcdriver's server machine: it serves the driver's service (package grpcdriver).
package main

import "github.com/mit-pdos/etcd-grove/examples/lib/grpcdriver"

func main() {
	grpcdriver.Server()
}
