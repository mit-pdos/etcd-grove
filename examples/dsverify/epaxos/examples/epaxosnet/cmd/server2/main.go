// Command server2 is the EPaxos kit's server machine 2 (package epaxosnet).
package main

import "github.com/imdea-software/swiftpaxos-epaxos/examples/epaxosnet"

func main() {
	epaxosnet.Server(2)
}
