// Command member is putget_safe's member machine's binary (notes/putget-dist-plan.md): putget.Member
// at the peer and client addresses given as its two arguments. The Lean boot program is
// putget.Member applied to the addresses' Go strings (the argument parsing is not translated: a
// trusted gap, as examples/etcd/dist/cmd's, review F15 of notes/etcd-dist-plan.md).
package main

import (
	"fmt"
	"os"

	"github.com/mit-pdos/etcd-grove/examples/etcd/dist/putget"
)

func main() {
	if len(os.Args) != 3 {
		fmt.Fprintln(os.Stderr, "usage: member PEER-ADDR CLIENT-ADDR")
		os.Exit(2)
	}
	putget.Member(os.Args[1], os.Args[2])
	fmt.Fprintln(os.Stderr, "member: a step failed")
	os.Exit(1)
}
