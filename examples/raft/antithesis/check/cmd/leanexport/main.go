// Command leanexport writes the differential test's fixtures for the Lean transcription of the
// checker (Proof/github_com/mit_pdos/etcd_grove/examples/raft/antithesis/check/Tla/, run by
// check/testdata/LeanDiff.lean): for each line of the verdicts files given, one JSON object per
// line with the configuration's constants, TLC's verdict, the Go checker's (check.Check) and the
// stream as the Go reader parsed it (check.Event, every field present only where the report has
// it), so that the Lean side decodes structure only and runs the same events as the Go.
//
//	leanexport testdata/verdicts.txt testdata/verdicts-fuzz.txt ... > fixtures.ndjson
package main

import (
	"bufio"
	"compress/gzip"
	"encoding/json"
	"fmt"
	"io"
	"os"
	"path/filepath"
	"strconv"
	"strings"

	"github.com/mit-pdos/etcd-grove/examples/raft/antithesis/check"
	"github.com/mit-pdos/etcd-grove/examples/raft/antithesis/check/ndjson"
)

func servers(n int) []string {
	var s []string
	for i := 1; i <= n; i++ {
		s = append(s, "raft"+strconv.Itoa(i))
	}
	return s
}

type cfgT struct {
	n, voters    int
	bootstrapped bool
}

var configs = map[string]cfgT{
	"EtcdBinding.cfg":       {3, 3, true},
	"EtcdBindingEmpty.cfg":  {3, 3, false},
	"EtcdBinding5.cfg":      {5, 5, true},
	"EtcdBinding5Empty.cfg": {5, 5, false},
	"EtcdBindingM.cfg":      {5, 3, true},
	"EtcdBindingMEmpty.cfg": {5, 3, false},
}

func value(v check.Value) map[string]any {
	return map[string]any{"isRec": v.IsRec, "str": v.Str, "add": nn(v.Add), "remove": nn(v.Remove),
		"joint": v.Joint, "leave": v.Leave}
}

func nn(s []string) []string {
	if s == nil {
		return []string{}
	}
	return s
}

func entries(es []check.Entry) []any {
	out := []any{}
	for _, e := range es {
		out = append(out, map[string]any{"term": e.Term, "type": e.Type, "value": value(e.Value)})
	}
	return out
}

func msg(m check.Msg) map[string]any {
	o := map[string]any{}
	put := func(bit uint32, k string, v any) {
		if m.Has&bit != 0 {
			o[k] = v
		}
	}
	put(check.MFType, "type", m.Type)
	put(check.MFFrom, "from", m.From)
	put(check.MFTo, "to", m.To)
	put(check.MFTerm, "term", m.Term)
	put(check.MFIndex, "index", m.Index)
	put(check.MFLogTerm, "logTerm", m.LogTerm)
	if m.Has&check.MFEntries != 0 {
		o["entries"] = entries(m.Entries)
	}
	put(check.MFCommit, "commit", m.Commit)
	put(check.MFReject, "reject", m.Reject)
	return o
}

func event(ev *check.Event) map[string]any {
	o := map[string]any{"e": ev.E, "node": ev.Node, "bad": ev.Bad,
		"b": ev.Has&check.FB != 0, "a": ev.Has&check.FA != 0}
	put := func(bit uint32, k string, v any) {
		if ev.Has&bit != 0 {
			o[k] = v
		}
	}
	put(check.FBy, "by", ev.By)
	put(check.FRole, "role", ev.Role)
	put(check.FTerm, "term", ev.Term)
	put(check.FVote, "vote", ev.Vote)
	put(check.FCommit, "commit", ev.Commit)
	put(check.FFirst, "first", ev.First)
	if ev.Has&check.FEntries != 0 {
		o["entries"] = entries(ev.Entries)
	}
	put(check.FLastIndex, "lastIndex", ev.LastIdx)
	put(check.FLastTerm, "lastTerm", ev.LastTerm)
	put(check.FApplied, "applied", ev.Applied)
	if ev.Has&check.FVoters != 0 {
		o["voters"] = nn(ev.Voters)
	}
	if ev.Has&check.FOutgoing != 0 {
		o["outgoing"] = nn(ev.Outgoing)
	}
	if ev.Has&check.FSnap != 0 {
		o["snap"] = map[string]any{"index": ev.Snap.Index, "term": ev.Snap.Term}
	}
	if ev.Has&check.FMsg != 0 {
		o["msg"] = msg(ev.Msg)
	}
	if ev.Has&check.FCause != 0 {
		c := []any{}
		for _, m := range ev.Cause {
			c = append(c, msg(m))
		}
		o["cause"] = c
	}
	put(check.FW, "w", ev.W)
	put(check.FMore, "more", ev.More)
	put(check.FIndex, "index", ev.Index)
	put(check.FCtx, "ctx", ev.Ctx)
	return o
}

func readStream(path string) ([]*check.Event, error) {
	f, err := os.Open(path)
	if err != nil {
		return nil, err
	}
	defer f.Close()
	var r io.Reader = f
	if strings.HasSuffix(path, ".gz") {
		z, err := gzip.NewReader(f)
		if err != nil {
			return nil, err
		}
		r = z
	}
	return ndjson.Read(r)
}

func main() {
	enc := json.NewEncoder(os.Stdout)
	for _, vf := range os.Args[1:] {
		f, err := os.Open(vf)
		if err != nil {
			fmt.Fprintln(os.Stderr, err)
			os.Exit(2)
		}
		sc := bufio.NewScanner(f)
		sc.Buffer(make([]byte, 1<<20), 1<<20)
		for sc.Scan() {
			fs := strings.SplitN(sc.Text(), " ", 5)
			if len(fs) < 5 {
				continue
			}
			c, ok := configs[fs[2]]
			if !ok {
				fmt.Fprintln(os.Stderr, "unknown configuration", fs[2])
				os.Exit(2)
			}
			path := filepath.Join(filepath.Dir(vf), fs[1])
			evs, err := readStream(path)
			if err != nil {
				fmt.Fprintln(os.Stderr, path, err)
				os.Exit(2)
			}
			cfg := &check.Config{Server: check.SetOf(servers(c.n)), InitVoters: check.SetOf(servers(c.voters)),
				Bootstrapped: c.bootstrapped}
			gov := check.Check(cfg, evs)
			out := []any{}
			for _, ev := range evs {
				out = append(out, event(ev))
			}
			kind := []string{"ACCEPTED", "REJECTED", "VIOLATED", "ERROR"}[gov.Kind]
			if err := enc.Encode(map[string]any{"file": fs[1], "cfg": fs[2], "servers": []string(cfg.Server),
				"voters": []string(cfg.InitVoters), "bootstrapped": c.bootstrapped, "tlc": fs[4],
				"go": map[string]any{"kind": kind, "k": gov.K, "names": nn(gov.Names)}, "events": out}); err != nil {
				fmt.Fprintln(os.Stderr, err)
				os.Exit(2)
			}
		}
		f.Close()
	}
}
