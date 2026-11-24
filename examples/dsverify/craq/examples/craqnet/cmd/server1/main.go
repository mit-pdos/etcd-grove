// Command server1 is the craq kit's server machine 1, the coordinator machine (package craqnet).
package main

import "github.com/despreston/go-craq/examples/craqnet"

func main() {
	craqnet.Server(1)
}
