// Command server is an etcd member machine's binary (notes/etcd-dist-plan.md, §2, §11.2): it reads
// the whole deployment (deployment.Deployment) as JSON from the file named by its first argument and
// its member's index from its second, then runs server.MainDeployment (Lean: serverProg d i), which
// checks the deployment first (deployment.WellFormed), returns at once if it fails, and otherwise
// runs member i (server.Main of its configuration). The argument and JSON parsing is not
// translated: a trusted gap (review F15); the Lean statement's boot program is
// server.MainDeployment applied to the deployment's Go value (the test writes the file from the
// same deployment). With DIST_LOG set, the member logs to standard error
// (server.MainDeploymentLogger), for the test's diagnosis.
package main

import (
	"encoding/json"
	"fmt"
	"os"
	"strconv"

	"go.uber.org/zap"

	"github.com/mit-pdos/etcd-grove/examples/etcd/dist/deployment"
	"github.com/mit-pdos/etcd-grove/examples/etcd/dist/server"
)

func main() {
	if len(os.Args) != 3 {
		fmt.Fprintln(os.Stderr, "usage: server DEPLOYMENT.json MEMBER")
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
	i, err := strconv.Atoi(os.Args[2])
	if err != nil {
		fmt.Fprintln(os.Stderr, err)
		os.Exit(2)
	}
	if os.Getenv("DIST_LOG") != "" {
		if lg, err := zap.NewDevelopment(); err == nil {
			server.MainDeploymentLogger(d, i, lg)
			return
		}
	}
	server.MainDeployment(d, i)
}
