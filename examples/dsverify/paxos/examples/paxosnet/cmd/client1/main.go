// Command client1 is the paxos kit's client machine 1 (package paxosnet).
package main

import "github.com/xiang90/paxos/examples/paxosnet"

func main() {
	paxosnet.Client(1)
}
