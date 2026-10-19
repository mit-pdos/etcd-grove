// Command kvcheck runs the replicated key-value store's randomized linearizability test:
// a cluster of replicas connected in process, clients running random Puts, Gets and
// Appends on random replicas, and porcupine's check of the trace. With no flags it runs
// kv.Main, the program the proof is about (Proof/github_com/mit_pdos/etcd_grove/examples/
// kv/Adequacy.lean: its porcupine check never fails). The flags run larger tests.
//
//	go run ./cmd/kvcheck                       # kv.Main
//	go run ./cmd/kvcheck -clients 16 -ops 200 -rounds 10 -clock monotonic
package main

import (
	"flag"
	"fmt"
	"os"
	"time"

	"github.com/anishathalye/porcupine"
	"github.com/mit-pdos/etcd-grove/examples/kv"
	"github.com/mit-pdos/etcd-grove/examples/lintest"
)

func main() {
	replicas := flag.Int("replicas", 3, "the cluster's voters")
	clients := flag.Int("clients", 0, "concurrent clients (0: run kv.Main)")
	ops := flag.Int("ops", 50, "operations per client")
	rounds := flag.Int("rounds", 1, "tests, each on a fresh cluster")
	clock := flag.String("clock", "counter", "the trace's clock: counter or monotonic")
	witness := flag.Bool("witness", false, "the last voter is a witness (StartClusterWitness)")
	flag.Parse()

	if *clients == 0 {
		start := time.Now()
		kv.Main()
		fmt.Printf("kv.Main: porcupine answered Ok (%v)\n", time.Since(start).Round(time.Millisecond))
		return
	}
	var voters []uint64
	for i := 1; i <= *replicas; i++ {
		voters = append(voters, uint64(i))
	}
	for i := 0; i < *rounds; i++ {
		c := lintest.CounterClock()
		if *clock == "monotonic" {
			c = lintest.MonotonicClock()
		}
		start := time.Now()
		var kvs []*kv.KV
		if *witness {
			kvs = kv.StartClusterWitness(voters[:len(voters)-1], voters[len(voters)-1])
		} else {
			kvs = kv.StartCluster(voters)
		}
		r := kv.Check(kvs, c, *clients, *ops)
		fmt.Printf("round %d: %d replicas, %d clients x %d operations: %v (%v)\n",
			i+1, *replicas, *clients, *ops, r, time.Since(start).Round(time.Millisecond))
		if r != porcupine.Ok {
			os.Exit(1)
		}
	}
}
