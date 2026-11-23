// Command client is putget_safe's client machine's binary (notes/putget-dist-plan.md): putget.Client
// against the member's client address, its one argument; it prints "checked" if the check ran, or
// "ended" if a step failed first. A failed check is a panic (exit status 2). The Lean boot program is
// putget.Client applied to the address's Go string (the argument parsing is not translated).
package main

import (
	"fmt"
	"os"

	"github.com/mit-pdos/etcd-grove/examples/etcd/dist/putget"
)

func main() {
	if len(os.Args) != 2 {
		fmt.Fprintln(os.Stderr, "usage: client CLIENT-ADDR")
		os.Exit(2)
	}
	if putget.Client(os.Args[1]) {
		fmt.Println("putget: checked")
	} else {
		fmt.Println("putget: ended")
	}
}
