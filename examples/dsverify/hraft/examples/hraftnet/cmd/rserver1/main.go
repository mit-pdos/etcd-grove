// Command rserver1 is the hraft kit's restartable server machine 1 (package rserver, ServerR;
// hraft_robust), over the data directory rserver.DataDir.
package main

import "github.com/hashicorp/raft/examples/hraftnet/rserver"

func main() {
	rserver.ServerR(1, rserver.DataDir)
}
