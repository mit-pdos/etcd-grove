// Command kvdurablecheck runs the durable reconfiguring key-value store's randomized test (the
// package's comment): a cluster of random options bootstrapped in process, each replica's raft
// storage in a file of a fresh temporary directory, clients running random Puts, Gets and Reads
// while proposers propose random configuration changes, replicas take snapshots and compact their
// logs at random, the network drops, duplicates, delays and reorders messages, leadership is
// disrupted, and replicas crash and restart from their files; then porcupine's check of the trace
// and a check that the members converge. With no flags it runs kvdurable.Main. The flags run more
// rounds, larger ones.
//
//	go run ./cmd/kvdurablecheck
//	go run ./cmd/kvdurablecheck -rounds 20 -clients 8 -ops 300 -proposers 3 -crash 20ms
package main

import (
	"flag"
	"fmt"
	"os"
	"time"

	"github.com/anishathalye/porcupine"
	"github.com/mit-pdos/etcd-grove/examples/kvdurable"
	"github.com/mit-pdos/etcd-grove/examples/lintest"
)

// tempDir is a fresh temporary directory; it exits on failure.
func tempDir() string {
	dir, err := os.MkdirTemp("", "kvdurable-")
	if err != nil {
		fmt.Println(err)
		os.Exit(1)
	}
	return dir
}

func main() {
	rounds := flag.Int("rounds", 0, "tests, each on a fresh cluster of random options (0: run kvdurable.Main)")
	clients := flag.Int("clients", 4, "concurrent clients")
	ops := flag.Int("ops", 100, "operations per client")
	proposers := flag.Int("proposers", 0, "concurrent proposers of configuration changes (0: random, 1 to 3)")
	reconf := flag.Duration("reconf", 10*time.Millisecond, "average pause between a proposer's proposals")
	disrupt := flag.Duration("disrupt", 30*time.Millisecond, "average pause between leadership disruptions (0: none)")
	crash := flag.Duration("crash", 40*time.Millisecond, "average pause between crashes (0: none)")
	clock := flag.String("clock", "counter", "the trace's clock: counter or monotonic")
	flag.Parse()

	if *rounds == 0 {
		dir := tempDir()
		start := time.Now()
		kvdurable.Main(dir)
		os.RemoveAll(dir)
		fmt.Printf("kvdurable.Main: porcupine answered Ok (%v)\n", time.Since(start).Round(time.Millisecond))
		return
	}
	for i := 0; i < *rounds; i++ {
		cfg := kvdurable.RandomConfig()
		cfg.Clients, cfg.Ops = *clients, *ops
		if *proposers != 0 {
			cfg.Proposers = *proposers
		}
		cfg.ReconfPause, cfg.DisruptPause, cfg.CrashPause = *reconf, *disrupt, *crash
		c := lintest.CounterClock()
		if *clock == "monotonic" {
			c = lintest.MonotonicClock()
		}
		dir := tempDir()
		start := time.Now()
		res, cl := kvdurable.Run(cfg, c, dir)
		err := cl.Converged(20 * time.Second)
		var dump string
		if err != nil {
			dump = cl.Dump()
		}
		cl.Stop()
		os.RemoveAll(dir)
		fmt.Printf("round %d: %+v, %d proposers, %d clients x %d operations: %v (%v)\n  %v\n",
			i+1, cfg.Options, cfg.Proposers, cfg.Clients, cfg.Ops, res, time.Since(start).Round(time.Millisecond), &cl.Stats)
		if res != porcupine.Ok || err != nil {
			if err != nil {
				fmt.Println(err)
				fmt.Print(dump)
			}
			os.Exit(1)
		}
	}
}
