// Command server is the probe's server node (netprobe.ServerMain), node 1 under the rig
// (../../rig.toml). It listens on the constant netprobe.ServerAddr.
package main

import "dsverify.lab/harness/netprobe"

func main() {
	netprobe.ServerMain()
}
