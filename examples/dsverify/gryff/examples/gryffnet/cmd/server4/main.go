// Command server4 is the gryff kit's server machine 4 (package gryffnet; 1: the master, else a replica).
package main

import "gryff/examples/gryffnet"

func main() {
	gryffnet.Server(4)
}
