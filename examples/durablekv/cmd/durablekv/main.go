// Command durablekv runs the durable replicated key-value store: a cluster of three replicas
// connected in process, each replica's raft state in a file of the data directory.
//
//	go run ./cmd/durablekv check                      # durablekv.Main on a fresh directory
//	go run ./cmd/durablekv check -clients 8 -ops 100 -rounds 5 -crash 50ms
//	go run ./cmd/durablekv put -dir /tmp/d k v        # each run starts the cluster on -dir,
//	go run ./cmd/durablekv append -dir /tmp/d k w     # runs one operation and exits
//	go run ./cmd/durablekv get -dir /tmp/d k          # without shutting down: a crash
//
// check runs the randomized linearizability test (durablekv.Check) with a random replica
// crashing and restarting every -crash; put, append and get show the store surviving the
// process's exit. Porcupine's search, not the store, limits check: past about 8 clients on the
// three keys it may not finish; and a -crash shorter than an election (50ms) starves progress.
package main

import (
	"flag"
	"fmt"
	"os"
	"time"

	"github.com/anishathalye/porcupine"
	"github.com/mit-pdos/etcd-grove/examples/durablekv"
	"github.com/mit-pdos/etcd-grove/examples/lintest"
)

func usage() {
	fmt.Fprintln(os.Stderr, "usage: durablekv check [flags] | put -dir D KEY VAL | append -dir D KEY VAL | get -dir D KEY")
	os.Exit(2)
}

func main() {
	if len(os.Args) < 2 {
		usage()
	}
	fs := flag.NewFlagSet(os.Args[1], flag.ExitOnError)
	dir := fs.String("dir", "", "the data directory (check: a fresh temporary one by default)")
	clients := fs.Int("clients", 0, "check: concurrent clients (0: run durablekv.Main)")
	ops := fs.Int("ops", 50, "check: operations per client")
	rounds := fs.Int("rounds", 1, "check: tests, each on a fresh cluster")
	crash := fs.Duration("crash", 50*time.Millisecond, "check: how often a random replica restarts (0: never)")
	fs.Parse(os.Args[2:])
	args := fs.Args()

	switch os.Args[1] {
	case "check":
		for i := 0; i < *rounds; i++ {
			d := *dir
			if d == "" || *rounds > 1 {
				var err error
				if d, err = os.MkdirTemp(*dir, "durablekv-"); err != nil {
					fmt.Fprintln(os.Stderr, err)
					os.Exit(1)
				}
				defer os.RemoveAll(d)
			}
			start := time.Now()
			if *clients == 0 {
				durablekv.Main(d)
				fmt.Printf("durablekv.Main: porcupine answered Ok (%v)\n", time.Since(start).Round(time.Millisecond))
				continue
			}
			c := durablekv.StartCluster(d, []uint64{1, 2, 3})
			r := durablekv.Check(c, lintest.MonotonicClock(), *clients, *ops, *crash)
			c.Stop()
			fmt.Printf("round %d: %d clients x %d operations, a restart every %v: %v (%v)\n",
				i+1, *clients, *ops, *crash, r, time.Since(start).Round(time.Millisecond))
			if r != porcupine.Ok {
				os.Exit(1)
			}
		}
	case "put", "append", "get":
		if *dir == "" || (os.Args[1] == "get" && len(args) != 1) || (os.Args[1] != "get" && len(args) != 2) {
			usage()
		}
		if err := os.MkdirAll(*dir, 0o755); err != nil {
			fmt.Fprintln(os.Stderr, err)
			os.Exit(1)
		}
		c := durablekv.StartCluster(*dir, []uint64{1, 2, 3})
		switch os.Args[1] {
		case "put":
			c.Put(1, args[0], args[1])
		case "append":
			c.Append(1, args[0], args[1])
		case "get":
			fmt.Println(c.Get(1, args[0]))
		}
		// exit without stopping the cluster: the replicas crash
	default:
		usage()
	}
}
