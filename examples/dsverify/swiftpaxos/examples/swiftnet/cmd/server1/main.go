// Command server1 is the swiftpaxos kit's server machine 1 (package swiftnet; 1 the master,
// 2.. the replicas).
package main

import "github.com/imdea-software/swiftpaxos/examples/swiftnet"

func main() {
	swiftnet.Server(1)
}
