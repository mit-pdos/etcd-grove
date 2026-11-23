// Command server5 is the swiftpaxos kit's server machine 5 (package swiftnet; 1 the master,
// 2.. the replicas).
package main

import "github.com/imdea-software/swiftpaxos/examples/swiftnet"

func main() {
	swiftnet.Server(5)
}
