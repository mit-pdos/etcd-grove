// fs-v2-r6 (b): minibolt's boot program as a plain Go main (initialize the package, call
// BootMinibolt(dir)), BOOTS times, so that its pwrite64 buffer addresses can be traced
// (addr.sh): NoTear.lean's program assumption says each is ≡ its file offset (mod 4096).
//
// Usage: addr DIR BOOTS
package main

import (
	"os"
	"strconv"

	"github.com/mit-pdos/etcd-grove/examples/osfs/bboltfs"
)

func main() {
	n, _ := strconv.Atoi(os.Args[2])
	for i := 0; i < n; i++ {
		bboltfs.BootMinibolt(os.Args[1])
	}
}
