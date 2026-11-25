// Command kvudp is command kvnet (cmd/kvnet) with the replicas' raft messages over UDP
// (kvnet.RunNodeUDP; the clients' requests still over TCP): kvudp's processes and its test.
//
//	kvudp node -id N -addrs HOST:PORT,... -dir DIR -voters V ...
//
// runs one replica (kvnet.RunNodeUDP with -transport udp, which check passes it) until its process is killed;
//
//	kvudp client -addrs HOST:PORT,... -voters V
//
// runs the checking client (kvcheck.Check): the harness starts these (driver.RunProcess).
//
//	kvudp check [-rounds N] [-crash kill|power|mixed] [-net netns|local] ...
//
// runs N rounds of the test (package driver), each on a fresh cluster of random options, every
// replica a process of this program on a machine of its own, and the checking client another, on
// a client machine. -net netns makes the machines network namespaces joined by a router, with the
// network's faults (partitions, resets, delay, loss, duplication, reordering:
// examples/lib/robust); it needs root, and the command runs itself again by sudo -n if it is not.
// -crash power and mixed make power losses: every replica on an ext4 filesystem of its own on a
// dm-flakey device, which needs sudo without a password. The defaults, auto, are netns and mixed if
// sudo is available, local and kill otherwise.
package main

import (
	"flag"
	"fmt"
	"os"
	"os/exec"
	"time"

	"github.com/anishathalye/porcupine"
	"github.com/mit-pdos/etcd-grove/examples/lib/robust"
	"github.com/mit-pdos/etcd-grove/examples/raft/kvnet/driver"
)

func main() {
	if len(os.Args) >= 2 && (os.Args[1] == driver.RoleNode || os.Args[1] == driver.RoleClient) {
		if err := driver.RunProcess(os.Args[1:]); err != nil {
			fmt.Fprintln(os.Stderr, err)
			os.Exit(2)
		}
		return
	}
	if len(os.Args) >= 2 && os.Args[1] == "check" {
		os.Exit(check(os.Args[2:]))
	}
	fmt.Fprintln(os.Stderr, "usage: kvudp node ... | kvudp client ... | kvudp check [flags]")
	os.Exit(2)
}

// check runs the test's rounds; its exit status.
func check(args []string) int {
	fs := flag.NewFlagSet("check", flag.ExitOnError)
	rounds := fs.Int("rounds", 1, "rounds, each on a fresh cluster of random options")
	crash := fs.String("crash", "auto", "crashes: kill (SIGKILL, syncfs), power (SIGKILL, the disk's power lost), mixed, or auto")
	voters := fs.Uint64("voters", 0, "the bootstrap configuration's voters (0: random, 1 to 5)")
	pause := fs.Duration("pause", 150*time.Millisecond, "average pause between crashes (0: none)")
	downtime := fs.Duration("downtime", 50*time.Millisecond, "a crashed replica stays down a random time below it")
	final := fs.Bool("final", true, "crash the whole cluster at once at the end")
	netMode := fs.String("net", "auto", "the machines: netns (network namespaces with network faults; root), local (one loopback address, no network faults), or auto")
	netPause := fs.Duration("netpause", 100*time.Millisecond, "average pause between network faults (0: none)")
	netHold := fs.Duration("nethold", 200*time.Millisecond, "how long a network fault lasts, on average")
	keep := fs.Bool("keep", false, "keep a failed round's work directory (logs, files)")
	fs.Parse(args)

	nm := *netMode
	if nm == "auto" {
		nm = "netns"
		if !robust.IsRoot() {
			if _, err := exec.Command("sudo", "-n", "true").CombinedOutput(); err != nil {
				fmt.Printf("no sudo (%v): local network, no network faults\n", err)
				nm = "local"
			}
		}
	}
	if nm == "netns" && !robust.IsRoot() {
		// the whole check as root: the namespaces, the dialing threads, the processes
		if err := robust.RerunAsRoot(append([]string{"check", "-net", "netns"}, args...), nil, os.Stdout); err != nil {
			if e, ok := err.(*exec.ExitError); ok {
				return e.ExitCode()
			}
			fmt.Println(err)
			return 1
		}
		return 0
	}
	mode := *crash
	if mode == "auto" {
		mode = driver.CrashMixed
		if err := robust.PowerAvailable(); err != nil {
			fmt.Printf("power losses unavailable (%v): kills only\n", err)
			mode = driver.CrashKill
		}
	}
	self, err := os.Executable()
	if err != nil {
		fmt.Println(err)
		return 1
	}
	cmd := driver.Command{Path: self}
	for i := 1; i <= *rounds; i++ {
		cfg := driver.RandomConfig(mode, nm == "netns")
		cfg.Transport = driver.TransportUDP
		cfg.NetPause, cfg.NetHold = *netPause, *netHold
		cfg.CrashPause, cfg.Downtime, cfg.FinalCrash = *pause, *downtime, *final
		if *voters != 0 {
			cfg.Voters = *voters
		}
		work, err := os.MkdirTemp("", "kvudp-")
		if err != nil {
			fmt.Println(err)
			return 1
		}
		start := time.Now()
		res, cl := driver.Run(cfg, cmd, work)
		var dump string
		if cl != nil && (res.Err != nil || res.Check != porcupine.Ok) {
			dump = cl.Dump()
		}
		if cl != nil {
			cl.Stop()
		}
		fmt.Printf("round %d: %+v, crashes %s, network %s, udp: porcupine %v (%v)\n",
			i, cfg.Options, mode, nm, res.Check, time.Since(start).Round(time.Millisecond))
		if cl != nil {
			fmt.Printf("  %v\n  network: %s\n", &cl.Stats, cl.NetStats())
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
