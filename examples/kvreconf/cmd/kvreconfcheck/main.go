// Command kvreconfcheck runs the reconfiguring key-value store's randomized test (the package's
// comment): a cluster of random options bootstrapped in process, clients running random Puts,
// Gets and Reads while proposers propose random configuration changes, replicas take snapshots
// and compact their logs at random, the network drops, duplicates, delays and reorders messages,
// and leadership is disrupted; then porcupine's check of the trace and a check that the members
// converge. With no flags it runs kvreconf.Main. The flags run more rounds, larger ones.
//
//	go run ./cmd/kvreconfcheck
//	go run ./cmd/kvreconfcheck -rounds 20 -clients 8 -ops 300 -proposers 3
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
	rounds := flag.Int("rounds", 0, "tests, each on a fresh cluster of random options (0: run kvreconf.Main)")
	clients := flag.Int("clients", 4, "concurrent clients")
	ops := flag.Int("ops", 100, "operations per client")
	proposers := flag.Int("proposers", 0, "concurrent proposers of configuration changes (0: random, 1 to 3)")
	reconf := flag.Duration("reconf", 10*time.Millisecond, "average pause between a proposer's proposals")
	disrupt := flag.Duration("disrupt", 30*time.Millisecond, "average pause between leadership disruptions (0: none)")
	clock := flag.String("clock", "counter", "the trace's clock: counter or monotonic")
	flag.Parse()

	if *rounds == 0 {
		start := time.Now()
		kvreconf.Main()
		fmt.Printf("kvreconf.Main: porcupine answered Ok (%v)\n", time.Since(start).Round(time.Millisecond))
		return
	}
	for i := 0; i < *rounds; i++ {
		cfg := kvreconf.RandomConfig()
		cfg.Clients, cfg.Ops = *clients, *ops
		if *proposers != 0 {
			cfg.Proposers = *proposers
		}
		cfg.ReconfPause, cfg.DisruptPause = *reconf, *disrupt
		c := lintest.CounterClock()
		if *clock == "monotonic" {
			c = lintest.MonotonicClock()
		}
		start := time.Now()
		res, cl := kvreconf.Run(cfg, c)
		err := cl.Converged(20 * time.Second)
		cl.Stop()
		fmt.Printf("round %d: %+v, %d proposers, %d clients x %d operations: %v (%v)\n  %v\n",
			i+1, cfg.Options, cfg.Proposers, cfg.Clients, cfg.Ops, res, time.Since(start).Round(time.Millisecond), &cl.Stats)
		if res != porcupine.Ok || err != nil {
			if err != nil {
				fmt.Println(err)
			}
			os.Exit(1)
		}
	}
}
