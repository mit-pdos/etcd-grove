// Command member is putgetK_safe's member machine's binary (notes/putget-dist-plan.md §13):
// putgetk.Member(i, peers, clients) for the arguments I PEER-0,...,PEER-k-1 CLIENT-0,...,CLIENT-k-1
// (the two lists comma-separated, the same on every member's machine). The Lean boot program is
// putgetk.Member applied to i and the two lists as Go slice literals (the argument parsing is not
// translated: a trusted gap, as examples/etcd/dist/putget's cmd).
package main

import (
	"fmt"
	"os"
	"strconv"
	"strings"

	"github.com/mit-pdos/etcd-grove/examples/etcd/dist/putgetk"
)

func main() {
	if len(os.Args) != 4 {
		fmt.Fprintln(os.Stderr, "usage: member I PEER-0,...,PEER-k-1 CLIENT-0,...,CLIENT-k-1")
		os.Exit(2)
	}
	i, err := strconv.ParseUint(os.Args[1], 10, 64)
	peers, clients := strings.Split(os.Args[2], ","), strings.Split(os.Args[3], ",")
	if err != nil || len(peers) != len(clients) || i >= uint64(len(peers)) {
		fmt.Fprintln(os.Stderr, "member: I must be below the number of members, the two lists of one length")
		os.Exit(2)
	}
	putgetk.Member(i, peers, clients)
	fmt.Fprintln(os.Stderr, "member: a step failed")
	os.Exit(1)
}
