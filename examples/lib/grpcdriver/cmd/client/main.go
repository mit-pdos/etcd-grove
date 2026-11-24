// Command client is grpcdriver's client machine: it makes random calls and streams and panics if a
// property gRPC guarantees fails (package grpcdriver).
package main

import "github.com/mit-pdos/etcd-grove/examples/lib/grpcdriver"

func main() {
	grpcdriver.Client()
}
