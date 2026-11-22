// Command server is an etcd member machine's binary (notes/etcd-dist-plan.md, §2): it reads its
// server.Config as JSON from the file named by its one argument and runs server.Main. The Lean
// statement's boot program is server.Main applied to the Config's Go value (the flag and JSON
// parsing is not translated: a trusted gap, review F15; the test writes the file from the same
// deployment the theorem quantifies over). With DIST_LOG set, the member logs to standard error
// (server.MainLogger), for the test's diagnosis.
package main

import (
	"encoding/json"
	"fmt"
	"os"

	"go.uber.org/zap"

	"github.com/mit-pdos/etcd-grove/examples/etcd/dist/server"
)

func main() {
	if len(os.Args) != 2 {
		fmt.Fprintln(os.Stderr, "usage: server CONFIG.json")
		os.Exit(2)
	}
	b, err := os.ReadFile(os.Args[1])
	if err != nil {
		fmt.Fprintln(os.Stderr, err)
		os.Exit(2)
	}
	var c server.Config
	if err := json.Unmarshal(b, &c); err != nil {
		fmt.Fprintln(os.Stderr, err)
		os.Exit(2)
	}
	if os.Getenv("DIST_LOG") != "" {
		lg, err := zap.NewDevelopment()
		if err == nil {
			server.MainLogger(c, lg)
			return
		}
	}
	server.Main(c)
}
