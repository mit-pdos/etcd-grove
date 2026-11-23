// Command client0 is the paxos kit's client machine 0 (package paxosnet).
package main

import "github.com/xiang90/paxos/examples/paxosnet"

func main() {
	paxosnet.Client(0)
}
