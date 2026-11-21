//go:build etcddist_sketch

// Command client is a client machine's binary (DRAFT sketch): its workload and the members'
// client endpoints as JSON from the file named by its one argument, then client.Main.
package main

import (
	"encoding/json"
	"os"

	"github.com/mit-pdos/etcd-grove/examples/etcd/dist/client"
)

type args struct {
	W   client.Workload
	Eps []string
}

func main() {
	b, err := os.ReadFile(os.Args[1])
	if err != nil {
		os.Exit(2)
	}
	var a args
	if err := json.Unmarshal(b, &a); err != nil {
		os.Exit(2)
	}
	client.Main(a.W, a.Eps)
}
