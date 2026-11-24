// Command client is a workload's orchestrator machine's binary (notes/etcd-dist-plan.md, §2,
// §11.2): it reads the whole deployment (deployment.Deployment) as JSON from the file named by its
// first argument and its workload's index from its second, then runs client.MainDeployment (Lean:
// clientProg d j), which checks the deployment first (deployment.WellFormed) and returns at once if
// it fails. It prints "set-up done" once the workload's set-up is done and the workload's result
// ("checked", or why it ended without a check). A failed check is a panic: the process exits with
// status 2 and Go's panic message. The argument and JSON parsing is not translated: a trusted gap
// (review F15); the Lean statement's program is client.MainDeployment applied to the deployment's
// Go value. The workload's client machines run cmd/node.
package main

import (
	"encoding/json"
	"fmt"
	"os"
	"strconv"

	"github.com/mit-pdos/etcd-grove/examples/etcd/dist/client"
	"github.com/mit-pdos/etcd-grove/examples/etcd/dist/deployment"
)

func main() {
	if len(os.Args) != 3 {
		fmt.Fprintln(os.Stderr, "usage: client DEPLOYMENT.json WORKLOAD")
		os.Exit(2)
	}
	b, err := os.ReadFile(os.Args[1])
	if err != nil {
		fmt.Fprintln(os.Stderr, err)
		os.Exit(2)
	}
	var d deployment.Deployment
	if err := json.Unmarshal(b, &d); err != nil {
		fmt.Fprintln(os.Stderr, err)
		os.Exit(2)
	}
	j, err := strconv.Atoi(os.Args[2])
	if err != nil {
		fmt.Fprintln(os.Stderr, err)
		os.Exit(2)
	}
	r := client.MainDeployment(d, j, func() { fmt.Println("set-up done") })
	fmt.Println(r)
}
