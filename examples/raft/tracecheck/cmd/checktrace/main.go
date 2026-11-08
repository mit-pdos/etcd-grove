// Command checktrace checks raft traces (NDJSON, the format of raft's TLA+ trace validation)
// against the Go transcription of raft's TLA+ specification: by the direct breadth-first checker
// (like TLC) and by porcupine.
//
//	go run ./raft/tracecheck/cmd/checktrace [-inv=false] [-porcupine=false] FILE...
package main

import (
	"flag"
	"fmt"
	"os"
	"time"

	"github.com/anishathalye/porcupine"
	"github.com/mit-pdos/etcd-grove/examples/raft/tracecheck/etcdraft"
)

func main() {
	inv := flag.Bool("inv", true, "check the invariants Traceetcdraft.cfg checks")
	usePorcupine := flag.Bool("porcupine", true, "also check with porcupine")
	explain := flag.Bool("explain", false, "on a failure, print the states before the failing line")
	flag.Parse()
	failed := false
	for _, file := range flag.Args() {
		f, err := os.Open(file)
		if err != nil {
			fmt.Fprintln(os.Stderr, err)
			os.Exit(2)
		}
		events, err := etcdraft.ReadNDJSON(f)
		f.Close()
		if err != nil {
			fmt.Fprintf(os.Stderr, "%s: %v\n", file, err)
			os.Exit(2)
		}
		t, err := etcdraft.NewTrace(events)
		if err != nil {
			fmt.Printf("%s: %v\n", file, err)
			failed = true
			continue
		}
		start := time.Now()
		r := etcdraft.CheckTrace(t, *inv)
		line := fmt.Sprintf("%s: %d events: direct: %v (%v)", file, t.Len(), r, time.Since(start).Round(time.Millisecond))
		if r.Violation == "" && !r.OK && r.Line > 0 {
			ev := t.Event(r.Line)
			line += fmt.Sprintf(" [line %d: %s nid %s]", r.Line, ev.Name, ev.NID)
		}
		if !r.OK {
			failed = true
		}
		if *usePorcupine {
			start = time.Now()
			p := etcdraft.CheckPorcupine(t, *inv, 0)
			line += fmt.Sprintf("; porcupine: %v (%v)", p, time.Since(start).Round(time.Millisecond))
			if p != porcupine.Ok {
				failed = true
			}
		}
		fmt.Println(line)
		if *explain && !r.OK {
			fmt.Print(etcdraft.Explain(t, r))
		}
	}
	if failed {
		os.Exit(1)
	}
}
