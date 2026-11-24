// Command server1 is the EPaxos kit's server machine 1 (package epaxosnet).
package main

import "github.com/imdea-software/swiftpaxos-epaxos/examples/epaxosnet"

func main() {
	epaxosnet.Server(1)
}
