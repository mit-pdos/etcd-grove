//go:build etcddist_sketch

// Command server is an etcd member machine's binary (DRAFT sketch): it reads its Config as JSON
// from the file named by its one argument and runs server.Main. The Lean statement's boot program
// is server.Main applied to the Config's Go value (the flag/JSON parsing is not translated: the
// harness, examples/lib/robust, writes the file from the same deployment the theorem quantifies over).
package main

import (
	"encoding/json"
	"os"

	"github.com/mit-pdos/etcd-grove/examples/etcd/dist/server"
)

func main() {
	b, err := os.ReadFile(os.Args[1])
	if err != nil {
		os.Exit(2)
	}
	var c server.Config
	if err := json.Unmarshal(b, &c); err != nil {
		os.Exit(2)
	}
	server.Main(c)
}
