// netpoll: os.OpenFile under a tiny RLIMIT_NOFILE (run.sh). Prints whether the file was created
// before the runtime's netpoller failed to initialize.
package main

import (
	"fmt"
	"os"
)

func main() {
	f, err := os.OpenFile(os.Args[1], os.O_RDWR|os.O_CREATE, 0o644)
	fmt.Println("returned", f != nil, err)
}
