// Command kvreconfcheck runs the reconfiguring key-value store's randomized test: a cluster
// bootstrapped in process, clients running random Puts, Gets and Reads while the cluster's
// membership changes at random (simple and joint changes), replicas take and install
// snapshots, and messages are dropped, replicas cut off and leadership moved; then
// porcupine's check of the trace and a check that the members converge. With no flags it runs
// kvreconf.Main. The flags run other tests.
//
//	go run ./cmd/kvreconfcheck
//	go run ./cmd/kvreconfcheck -clients 8 -ops 300 -rounds 10 -drop 20
package main

import (
	"flag"
	"fmt"
	"os"
	"time"

	"github.com/anishathalye/porcupine"
	"github.com/mit-pdos/etcd-grove/examples/kvreconf"
	"github.com/mit-pdos/etcd-grove/examples/lintest"
)

func main() {
	def := kvreconf.DefaultConfig()
	clients := flag.Int("clients", 0, "concurrent clients (0: run kvreconf.Main)")
	ops := flag.Int("ops", def.Ops, "operations per client")
	rounds := flag.Int("rounds", 1, "tests, each on a fresh cluster")
	drop := flag.Uint64("drop", def.DropOneIn, "drop one message in N (0: none)")
	reconf := flag.Duration("reconf", def.ReconfPause, "pause between configuration changes")
	faults := flag.Duration("faults", def.FaultPause, "pause between faults (0: none)")
	prevote := flag.Bool("prevote", def.PreVote, "raft's PreVote")
	checkquorum := flag.Bool("checkquorum", def.CheckQuorum, "raft's CheckQuorum")
	clock := flag.String("clock", "counter", "the trace's clock: counter or monotonic")
	flag.Parse()

	if *clients == 0 {
		start := time.Now()
		kvreconf.Main()
		fmt.Printf("kvreconf.Main: porcupine answered Ok, members converged (%v)\n", time.Since(start).Round(time.Millisecond))
		return
	}
	cfg := def
	cfg.Clients, cfg.Ops = *clients, *ops
	cfg.DropOneIn, cfg.ReconfPause, cfg.FaultPause = *drop, *reconf, *faults
	cfg.PreVote, cfg.CheckQuorum = *prevote, *checkquorum
	for i := 0; i < *rounds; i++ {
		c := lintest.CounterClock()
		if *clock == "monotonic" {
			c = lintest.MonotonicClock()
		}
		start := time.Now()
		res, err, cl := kvreconf.Run(cfg, c)
		fmt.Printf("round %d: %d clients x %d operations: %v (%v)\n  %v\n",
			i+1, *clients, *ops, res, time.Since(start).Round(time.Millisecond), &cl.Stats)
		if res != porcupine.Ok || err != nil {
			if err != nil {
				fmt.Println(err)
			}
			os.Exit(1)
		}
	}
}
