// Command overlay writes the conformance tracer's `go build -overlay` file under DIR and prints
// its path (examples/net/conform/README.md):
//
//	go build -overlay "$(go run ./net/conform/cmd/overlay DIR)" -o server ./net/echo/cmd/server
package main

import (
	"fmt"
	"os"

	"github.com/mit-pdos/etcd-grove/examples/net/conform/overlay"
)

func main() {
	if len(os.Args) != 2 {
		fmt.Fprintln(os.Stderr, "usage: overlay DIR")
		os.Exit(2)
	}
	p, err := overlay.Make(os.Args[1])
	if err != nil {
		fmt.Fprintln(os.Stderr, err)
		os.Exit(1)
	}
	fmt.Println(p)
}
