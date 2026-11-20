// Command client is the probe's client node (netprobe.ClientMain), node 0 under the rig
// (../../rig.toml). It exits 0 if the echo checks, and by a panic otherwise.
package main

import (
	"fmt"

	"dsverify.lab/harness/netprobe"
)

func main() {
	netprobe.ClientMain()
	fmt.Println("netprobe: echo checked")
}
