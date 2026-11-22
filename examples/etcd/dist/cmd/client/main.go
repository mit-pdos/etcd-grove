// Command client is a client machine's binary (notes/etcd-dist-plan.md, §2): its workload and the
// members' client endpoints as JSON (Args) from the file named by its one argument, then
// client.Main (the workload's orchestrator, or its only machine), or client.NodeMain on one of the
// workload's client machines (Args.IsNode), which serves the orchestrator's calls and never
// returns. The orchestrator prints "set-up done" once the workload's set-up is done
// (client.MainReady) and the workload's result ("checked", or why it ended without a check). A
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
	if a.IsNode {
		if a.Node < 0 || a.Node >= len(a.Nodes) {
			fmt.Fprintln(os.Stderr, "client: no such client machine")
			os.Exit(2)
		}
		client.NodeMain(a.W, a.Node, a.Nodes[a.Node], a.Eps)
		fmt.Fprintln(os.Stderr, "client: NodeMain returned")
		os.Exit(2)
	}
	r := client.MainReady(a.W, a.Eps, a.Nodes, func() { fmt.Printf("%s: set-up done\n", a.W.Kind) })
	fmt.Printf("%s: %v\n", a.W.Kind, r)
}
