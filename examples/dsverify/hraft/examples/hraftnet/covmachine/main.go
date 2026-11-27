//go:build covmachine

// Command covmachine is one machine of the hraft kit's deployment, for the multi-process runs of
// examples/dsverify/hraftrobust (not in the kit's build: tag covmachine): `covmachine
// <server1..6|client0..4|orch>` runs that machine's program (hraftnet.Server, Client, Orch, as its
// command of ../cmd does). Built with -cover -covermode=atomic and run with GOCOVERDIR set, it
// writes its coverage counters there every 200 ms and on SIGTERM (a machine is killed, never
// ends). With HRAFTNET_WARM=MS, the orchestrator is hraftnet.WarmOrch(MS, OPS), OPS from
// HRAFTNET_OPS (default 8: the tests' small workload).
package main

import (
	"os"
	"os/signal"
	"runtime/coverage"
	"strconv"
	"strings"
	"syscall"
	"time"

	"github.com/hashicorp/raft/examples/hraftnet"
)

func main() {
	if len(os.Args) != 2 {
		panic("usage: covmachine <server1..6|client0..4|orch>")
	}
	d := os.Getenv("GOCOVERDIR")
	if d != "" {
		flush(d)
	}
	w := os.Args[1]
	switch {
	case w == "orch":
		if ms, err := strconv.ParseUint(os.Getenv("HRAFTNET_WARM"), 10, 64); err == nil && ms > 0 {
			ops, err := strconv.ParseUint(os.Getenv("HRAFTNET_OPS"), 10, 64)
			if err != nil || ops == 0 {
				ops = 8
			}
			hraftnet.WarmOrch(ms, ops)
		} else {
			hraftnet.Orch()
		}
		if d != "" {
			coverage.WriteCountersDir(d)
		}
	case strings.HasPrefix(w, "client"):
		c, err := strconv.ParseUint(w[6:], 10, 64)
		if err != nil {
			panic(err)
		}
		hraftnet.Client(c)
	case strings.HasPrefix(w, "server"):
		id, err := strconv.ParseUint(w[6:], 10, 64)
		if err != nil {
			panic(err)
		}
		hraftnet.Server(id)
	default:
		panic("covmachine: no machine " + w)
	}
}

// flush writes the binary's coverage metadata to d (if no machine did yet), then its counters
// every 200 ms and on SIGTERM.
func flush(d string) {
	coverage.WriteMetaDir(d)
	term := make(chan os.Signal, 1)
	signal.Notify(term, syscall.SIGTERM)
	go func() {
		for {
			select {
			case <-term:
				coverage.WriteCountersDir(d)
				os.Exit(0)
			case <-time.After(200 * time.Millisecond):
				coverage.WriteCountersDir(d)
			}
		}
	}()
}
