// Command client is putgetK_safe's client machine's binary (notes/putget-dist-plan.md §13):
// putgetk.Client against member 0's client address, its one argument; it prints "checked" if the
// check ran, or "ended" if a step failed first. A failed check is a panic (exit status 2). The Lean
// boot program is putgetk.Client applied to the address's Go string (the argument parsing is not
// translated).
package main

import (
	"fmt"
	"os"

	"github.com/mit-pdos/etcd-grove/examples/etcd/dist/putgetk"
)

func main() {
	if len(os.Args) != 2 {
		fmt.Fprintln(os.Stderr, "usage: client CLIENT-ADDR")
		os.Exit(2)
	}
	if putgetk.Client(os.Args[1]) {
		fmt.Println("putgetk: checked")
	} else {
		fmt.Println("putgetk: ended")
	}
}
