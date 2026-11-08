// Command checktrace checks raft traces (NDJSON, the format of raft's TLA+ trace validation)
// against the Go transcription of raft's TLA+ specification: by the direct breadth-first checker
// (like TLC) and by porcupine.
//
//	go run ./raft/tracecheck/cmd/checktrace [-inv=false] [-porcupine=false] FILE...
package main

import (
	"encoding/json"
	"flag"
	"fmt"
	"os"
	"time"

	"github.com/anishathalye/porcupine"
	"github.com/mit-pdos/etcd-grove/examples/raft/tracecheck/etcdraft"
	"github.com/mit-pdos/etcd-grove/examples/raft/tracecheck/etcdraft/ndjson"
	"github.com/mit-pdos/etcd-grove/examples/raft/tracecheck/etcdraft/pmodel"
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
		events, err := ndjson.ReadNDJSON(f)
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
		if r.Violation == "" && r.EvalError == "" && !r.OK && r.Line > 0 {
			ev := t.Event(r.Line)
			line += fmt.Sprintf(" [line %d: %s nid %s]", r.Line, ev.Name, ev.NID)
		}
		if !r.TLCOK() {
			failed = true
		}
		if *usePorcupine {
			start = time.Now()
			p := pmodel.CheckPorcupine(t, *inv, 0)
			line += fmt.Sprintf("; porcupine: %v (%v)", p, time.Since(start).Round(time.Millisecond))
			if p != porcupine.Ok {
				failed = true
			}
		}
		fmt.Println(line)
		if *explain && !r.OK {
			fmt.Print(explainFailure(t, r))
		}
	}
	if failed {
		os.Exit(1)
	}
}

// explainFailure describes why no state of r.Before steps through r.Line: the line, and for each state
// the variables of the line's node and, for a received message's line, the messages in transit to
// it.
func explainFailure(t *etcdraft.Trace, r etcdraft.Result) string {
	if r.OK || r.Line == 0 {
		return ""
	}
	ev := t.Event(r.Line)
	b, _ := json.Marshal(ev)
	out := fmt.Sprintf("line %d: %s\n", r.Line, b)
	for k, ts := range r.Before {
		out += fmt.Sprintf("state %d of %d (pl %d):\n%s", k+1, len(r.Before), ts.PL, ts.S)
		if ev.Msg != nil {
			for _, m := range ts.S.Messages.Domain() {
				if fmt.Sprint(m.Dest) == ev.Msg.To {
					out += fmt.Sprintf("  in transit: %v x%d\n", m, ts.S.Messages.Count(m))
				}
			}
		}
	}
	return out
}
