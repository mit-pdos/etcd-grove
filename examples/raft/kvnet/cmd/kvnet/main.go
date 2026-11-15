// Command kvnet runs kvnet's replicas and its test.
//
//	kvnet node -id N -dir DIR -addrs 1=HOST:PORT,... -voters V ...
//
// runs one replica (kvnet.RunNode) until its process is killed; the driver starts these.
//
//	kvnet check [-rounds N] [-crash kill|power|mixed] [-clients C] [-ops O] ...
//
// runs N rounds of the test (package driver), each on a fresh cluster of random options, every
// replica a process of this program. -crash power and mixed make power losses: every replica on
// an ext4 filesystem of its own on a dm-flakey device, which needs sudo without a password (the
// default, auto, is mixed if that is available and kill otherwise).
package main

import (
	"flag"
	"fmt"
	"os"
	"time"

	"github.com/anishathalye/porcupine"
	"github.com/mit-pdos/etcd-grove/examples/lib/lintest"
	"github.com/mit-pdos/etcd-grove/examples/raft/kvnet"
	"github.com/mit-pdos/etcd-grove/examples/raft/kvnet/driver"
)

func main() {
	if len(os.Args) >= 2 && os.Args[1] == "node" {
		cfg, err := kvnet.ParseNodeArgs(os.Args[2:])
		if err != nil {
			fmt.Fprintln(os.Stderr, err)
			os.Exit(2)
		}
		kvnet.RunNode(cfg)
		return
	}
	if len(os.Args) >= 2 && os.Args[1] == "check" {
		os.Exit(check(os.Args[2:]))
	}
	fmt.Fprintln(os.Stderr, "usage: kvnet node ... | kvnet check [flags]")
	os.Exit(2)
}

// check runs the test's rounds; its exit status.
func check(args []string) int {
	fs := flag.NewFlagSet("check", flag.ExitOnError)
	rounds := fs.Int("rounds", 1, "rounds, each on a fresh cluster of random options")
	crash := fs.String("crash", "auto", "crashes: kill (SIGKILL, syncfs), power (SIGKILL, the disk's power lost), mixed, or auto")
	clients := fs.Int("clients", 4, "concurrent clients")
	ops := fs.Int("ops", 100, "operations per client")
	proposers := fs.Int("proposers", 0, "concurrent proposers of configuration changes (0: random, 1 to 3)")
	voters := fs.Uint64("voters", 0, "the bootstrap configuration's voters (0: random, 1 to 5)")
	pause := fs.Duration("pause", 150*time.Millisecond, "average pause between crashes (0: none)")
	downtime := fs.Duration("downtime", 50*time.Millisecond, "a crashed replica stays down a random time below it")
	final := fs.Bool("final", true, "crash the whole cluster at once at the end")
	faults := fs.Bool("faults", true, "the transport drops, delays, duplicates messages and cuts connections")
	keep := fs.Bool("keep", false, "keep a failed round's work directory (logs, files)")
	clock := fs.String("clock", "counter", "the trace's clock: counter or monotonic")
	fs.Parse(args)

	mode := *crash
	if mode == "auto" {
		mode = driver.CrashMixed
		if err := driver.PowerAvailable(); err != nil {
			fmt.Printf("power losses unavailable (%v): kills only\n", err)
			mode = driver.CrashKill
		}
	}
	self, err := os.Executable()
	if err != nil {
		fmt.Println(err)
		return 1
	}
	cmd := driver.Command{Path: self, Args: []string{"node"}}
	for i := 1; i <= *rounds; i++ {
		cfg := driver.RandomConfig(mode)
		cfg.Clients, cfg.Ops, cfg.CrashPause, cfg.Downtime, cfg.FinalCrash = *clients, *ops, *pause, *downtime, *final
		if *proposers != 0 {
			cfg.Proposers = *proposers
		}
		if *voters != 0 {
			cfg.Voters = *voters
		}
		if !*faults {
			cfg.Faults = kvnet.Faults{}
		}
		c := lintest.CounterClock()
		if *clock == "monotonic" {
			c = lintest.MonotonicClock()
		}
		work, err := os.MkdirTemp("", "kvnet-")
		if err != nil {
			fmt.Println(err)
			return 1
		}
		start := time.Now()
		res, cl := driver.Run(cfg, cmd, work, c)
		var dump string
		if cl != nil && (res.Err != nil || res.Check != porcupine.Ok) {
			dump = cl.Dump()
		}
		if cl != nil {
			cl.Stop()
		}
		fmt.Printf("round %d: %+v, crashes %s, %d proposers, %d clients x %d operations: porcupine %v (%v)\n",
			i, cfg.Options, mode, cfg.Proposers, cfg.Clients, cfg.Ops, res.Check, time.Since(start).Round(time.Millisecond))
		if cl != nil {
			fmt.Printf("  %v\n", &cl.Stats)
		}
		if res.Err != nil || res.Check != porcupine.Ok {
			if res.Err != nil {
				fmt.Println(res.Err)
			}
			fmt.Print(dump)
			if *keep {
				fmt.Println("work directory kept:", work)
			} else {
				os.RemoveAll(work)
			}
			return 1
		}
		os.RemoveAll(work)
	}
	return 0
}
