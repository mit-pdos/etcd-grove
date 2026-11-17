// Command leanexport writes a trace (NDJSON) as a Lean file that runs the Lean transcription's
// checker on it (`Proof/.../tracecheck/etcdraft/Tla/Check.lean`), for comparing its verdict with the
// Go checker's and TLC's (notes/trace-validation-plan.md, S2); PREVOTE and CHECKQUORUM ("1") as
// TLC reads them. Not translated.
//
//	go run ./cmd/leanexport FILE.ndjson > /tmp/x.lean && lake env lean /tmp/x.lean
package main

import (
	"bufio"
	"fmt"
	"os"
	"strconv"
	"strings"

	"github.com/mit-pdos/etcd-grove/examples/raft/tracecheck/etcdraft"
	"github.com/mit-pdos/etcd-grove/examples/raft/tracecheck/etcdraft/ndjson"
)

func str(s string) string { return strconv.Quote(s) }

func strs(l []string) string {
	q := make([]string, len(l))
	for k, s := range l {
		q[k] = str(s)
	}
	return "[" + strings.Join(q, ", ") + "]"
}

func event(ev *etcdraft.Event) string {
	var b strings.Builder
	fmt.Fprintf(&b, "{ name := %s, nid := %s, state := { term := %d, vote := %s, commit := %d }, role := %s, log := %d, conf := (%s, %s), ",
		str(ev.Name), str(ev.NID), ev.State.Term, str(ev.State.Vote), ev.State.Commit, str(ev.Role), ev.Log,
		strs(ev.Conf[0]), strs(ev.Conf[1]))
	if m := ev.Msg; m != nil {
		fmt.Fprintf(&b, "msg := some { type := %s, term := %d, «from» := %s, to := %s, entries := %d, logTerm := %d, index := %d, commit := %d, vote := %s, reject := %t, rejectHint := %d }, ",
			str(m.Type), m.Term, str(m.From), str(m.To), m.Entries, m.LogTerm, m.Index, m.Commit, str(m.Vote), m.Reject, m.RejectHint)
	} else {
		b.WriteString("msg := none, ")
	}
	if p := ev.Prop; p != nil {
		if cc := p.CC; cc != nil {
			changes := "none"
			if cc.Changes != nil {
				var cs []string
				for _, c := range *cc.Changes {
					cs = append(cs, fmt.Sprintf("{ nid := %s, action := %s }", str(c.NID), str(c.Action)))
				}
				changes = "some [" + strings.Join(cs, ", ") + "]"
			}
			newconf := "none"
			if cc.NewConf != nil {
				newconf = "some " + strs(*cc.NewConf)
			}
			fmt.Fprintf(&b, "prop := some { cc := some { changes := %s, newconf := %s } } }", changes, newconf)
		} else {
			b.WriteString("prop := some { cc := none } }")
		}
	} else {
		b.WriteString("prop := none }")
	}
	return b.String()
}

func main() {
	f, err := os.Open(os.Args[1])
	if err != nil {
		panic(err)
	}
	events, err := ndjson.ReadNDJSON(f)
	if err != nil {
		panic(err)
	}
	w := bufio.NewWriter(os.Stdout)
	defer w.Flush()
	fmt.Fprintln(w, "import Proof.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Tla.Check")
	fmt.Fprintln(w, "open Perennial.EtcdGrove.Etcdraft")
	fmt.Fprintln(w, "set_option maxRecDepth 100000")
	fmt.Fprintln(w, "def events : List Event := [")
	for k := range events {
		sep := ","
		if k == len(events)-1 {
			sep = ""
		}
		fmt.Fprintf(w, "  %s%s\n", event(&events[k]), sep)
	}
	fmt.Fprintln(w, "]")
	flag := func(name string) string {
		if v := os.Getenv(name); v == "1" || v == "true" {
			return "true"
		}
		return "false"
	}
	fmt.Fprintf(w, "#eval match newTraceWith events %s %s with\n", flag("PREVOTE"), flag("CHECKQUORUM"))
	fmt.Fprintln(w, `
  | .error e => s!"refused: {repr e}"
  | .ok t => let r := checkTrace t true; s!"tlcOK {r.tlcOK} ok {r.ok} branched {r.branched} line {r.line} violation {r.violation} evalError {repr r.evalError}"`)
}
