// Command server4 is the paxos kit's server machine 4 (package paxosnet).
package main

import "github.com/xiang90/paxos/examples/paxosnet"

func main() {
	paxosnet.Server(4)
}
