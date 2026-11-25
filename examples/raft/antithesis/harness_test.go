package antithesis

import (
	"fmt"
	"os"
	"path/filepath"
	"strconv"
	"testing"

	"github.com/mit-pdos/etcd-grove/examples/raft/antithesis/check"
	"github.com/mit-pdos/etcd-grove/examples/raft/antithesis/check/ndjson"
)

// TestRuns is the non-vacuity test of Main: RUNS runs (default 50) of DefaultConfig, each of whose
// streams must be accepted by Antithesis's model (check.Check, Main's check.Run without its
// panics), must commit some entries (an `apply` report) and must have every node record at least
// one `ready`. KEEP=dir writes every stream there (run-<k>.ndjson), for TLC
// (check/testdata/tlc-dir.sh).
func TestRuns(t *testing.T) {
	runs := 50
	if s := os.Getenv("RUNS"); s != "" {
		var err error
		if runs, err = strconv.Atoi(s); err != nil {
			t.Fatalf("RUNS=%q: %v", s, err)
		}
	}
	keep := os.Getenv("KEEP")
	accepted := 0
	for k := 1; k <= runs; k++ {
		c := RunCluster(DefaultConfig())
		evs := c.Events()
		cfg := &check.Config{Server: c.Servers(), InitVoters: c.Servers(), Bootstrapped: false}
		v := check.Check(cfg, evs)
		if keep != "" || v.Kind != check.Accepted {
			dir := keep
			if dir == "" {
				dir = t.TempDir()
			}
			p := filepath.Join(dir, fmt.Sprintf("run-%d.ndjson", k))
			f, err := os.Create(p)
			if err != nil {
				t.Fatal(err)
			}
			if err := ndjson.Write(f, evs); err != nil {
				t.Fatal(err)
			}
			f.Close()
			if v.Kind != check.Accepted {
				t.Errorf("run %d: %v (%d events; stream %s)", k, v, len(evs), p)
				continue
			}
		}
		accepted++
		s := summarize(evs)
		if s.applies == 0 {
			t.Errorf("run %d: nothing committed (no apply report; %d events)", k, len(evs))
		}
		for _, name := range names(c.cfg.Nodes) {
			if s.readies[name] == 0 {
				t.Errorf("run %d: node %s recorded no ready (%d events)", k, name, len(evs))
			}
		}
		t.Logf("run %d: %v; %s", k, v, s)
	}
	t.Logf("%d of %d accepted", accepted, runs)
}

// summary is what a stream shows of a run: its size, the reports per kind, the leaders elected
// (a `ready` whose role is leader, per term) and the highest term.
type summary struct {
	events, applies, applied int
	readies                  map[string]int
	leaders                  map[int]string
	maxTerm                  int
}

func summarize(evs []*check.Event) summary {
	s := summary{events: len(evs), readies: map[string]int{}, leaders: map[int]string{}}
	for _, ev := range evs {
		switch ev.E {
		case "ready":
			s.readies[ev.Node]++
			if ev.Role == "leader" {
				s.leaders[ev.Term] = ev.Node
			}
			if ev.Term > s.maxTerm {
				s.maxTerm = ev.Term
			}
		case "apply":
			s.applies++
			s.applied += len(ev.Entries)
		}
	}
	return s
}

func (s summary) String() string {
	return fmt.Sprintf("%d events, %d applies (%d entries), %d leaders, max term %d", s.events, s.applies,
		s.applied, len(s.leaders), s.maxTerm)
}
