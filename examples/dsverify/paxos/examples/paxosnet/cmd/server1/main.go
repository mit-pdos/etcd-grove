// Command server1 is the paxos kit's server machine 1 (package paxosnet).
package main

import "github.com/xiang90/paxos/examples/paxosnet"

func main() {
	paxosnet.Server(1)
}
