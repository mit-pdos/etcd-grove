// Command node is a workload's client machine's binary (notes/etcd-dist-plan.md, §2 and D8,
// §11.2): it reads the whole deployment (deployment.Deployment) as JSON from the file named by its
// first argument and its index among the deployment's client machines (in deployment.Deployment.Node's
// order: the workloads' order, then the index within the workload) from its second, then runs
// client.NodeDeployment (Lean: nodeProg d n), which checks the deployment first
// (deployment.WellFormed), returns at once if it fails, and otherwise serves the workload's
// orchestrator's calls and never returns. The argument and JSON parsing is not translated: a
// trusted gap (review F15).
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
		fmt.Fprintln(os.Stderr, "usage: node DEPLOYMENT.json N")
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
	n, err := strconv.Atoi(os.Args[2])
	if err != nil {
		fmt.Fprintln(os.Stderr, err)
		os.Exit(2)
	}
	client.NodeDeployment(d, n)
	fmt.Fprintln(os.Stderr, "node: client.NodeDeployment returned")
	os.Exit(2)
}
