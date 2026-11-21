// Command client is a client machine's binary (notes/etcd-dist-plan.md, §2): its workload and the
// members' client endpoints as JSON (Args) from the file named by its one argument, then
// client.Main; it prints the workload's result ("checked", or why it ended without a check). A
// failed check is a panic: the process exits with status 2 and Go's panic message.
package main

import (
	"encoding/json"
	"fmt"
	"os"

	"github.com/mit-pdos/etcd-grove/examples/etcd/dist/client"
)

func main() {
	if len(os.Args) != 2 {
		fmt.Fprintln(os.Stderr, "usage: client ARGS.json")
		os.Exit(2)
	}
	b, err := os.ReadFile(os.Args[1])
	if err != nil {
		fmt.Fprintln(os.Stderr, err)
		os.Exit(2)
	}
	var a client.Args
	if err := json.Unmarshal(b, &a); err != nil {
		fmt.Fprintln(os.Stderr, err)
		os.Exit(2)
	}
	fmt.Printf("%s: %v\n", a.W.Kind, client.Main(a.W, a.Eps))
}
