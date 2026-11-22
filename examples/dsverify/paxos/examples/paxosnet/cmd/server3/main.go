// Command server3 is the paxos kit's server machine 3 (package paxosnet).
package main

import "github.com/xiang90/paxos/examples/paxosnet"

func main() {
	paxosnet.Server(3)
}
