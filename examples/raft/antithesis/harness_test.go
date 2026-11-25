package antithesis

import (
	"fmt"
	"os"
	"path/filepath"
	"sort"
	"strconv"
	"testing"

	"github.com/mit-pdos/etcd-grove/examples/raft/antithesis/check"
	"github.com/mit-pdos/etcd-grove/examples/raft/antithesis/check/ndjson"
)

// The non-vacuity tests of Main. Each runs RUNS runs (default 100) of a family of modes, each
// drawn as DrawMode draws it with some flags fixed; every stream must be accepted by Antithesis's
// model (check.Check, Main's check.Run without its panics), and over the family every behaviour
// the family turns on must be reached (a read served, a conf change applied, a restart, a
// snapshot restored, a leader change, entries applied). Each logs its acceptance per mode flag.
// KEEP=dir writes every stream there; REJECTS=dir writes each rejected stream there (with its
// mode), for minimizing and for TLC (check/testdata/tlc-dir.sh).

func runs(t *testing.T) int {
	n := 100
	if s := os.Getenv("RUNS"); s != "" {
		var err error
		if n, err = strconv.Atoi(s); err != nil {
			t.Fatalf("RUNS=%q: %v", s, err)
		}
	}
	return n
}

// FullScope is every feature on (the plain theorem's scope); B1Scope is batch B1's (messages and N
// servers: no restarts, AsyncStorageWrites, batching, parallel or split writes, snapshots or
// membership changes).
func FullScope() Scope {
	return Scope{PreVote: true, CheckQuorum: true, Reads: true, Transfer: true, Forwarding: true, Dup: true,
		NonVoters: true, Boot: true, Limits: true, Restarts: true, Async: true, Batch: true, Parallel: true,
		Split: true, Snapshots: true, ConfChanges: true}
}

func B1Scope() Scope {
	s := FullScope()
	s.Restarts, s.Async, s.Batch, s.Parallel, s.Split, s.Snapshots, s.ConfChanges = false, false, false, false,
		false, false, false
	return s
}

// family is a set of modes: DrawMode within scope, then fix.
type family struct {
	name  string
	scope Scope
	fix   func(*Mode)
	cfg   func(*Config)
	// need: the paths every run of the family together must reach.
	need []string
	// expectRejects: the family shows a known rejection (a reproducer), not a failure.
	expectRejects bool
}

func syncOnly(m *Mode) {
	m.Async, m.Batch, m.Parallel, m.Split = false, false, false, splitNone
}

var families = []family{
	{name: "b1", scope: B1Scope(), fix: func(m *Mode) {},
		need: []string{"apply", "leaderChange", "read"}},
	{name: "full", scope: FullScope(), fix: func(m *Mode) {},
		need: []string{"apply", "leaderChange", "read", "restart", "conf", "restore", "async", "batch"}},
	{name: "durable", scope: FullScope(), // B2's: restarts, async, batching, parallel, split orders
		fix: func(m *Mode) {
			m.Restarts, m.Snapshots, m.ConfChanges = true, false, false
		}, need: []string{"apply", "leaderChange", "restart", "async", "batch"}},
	{name: "snapconf", scope: FullScope(), // B3's: snapshots and membership
		fix: func(m *Mode) {
			m.Snapshots, m.ConfChanges = true, true
		}, need: []string{"apply", "leaderChange", "conf", "restore", "snap"}},
	{name: "asyncsnapconf", scope: FullScope(), // where plan §2(c) expects the snapshot-config divergence
		fix: func(m *Mode) {
			m.Async, m.Batch, m.Parallel, m.Split = true, false, false, splitNone
			m.Snapshots, m.ConfChanges, m.Restarts = true, true, true
		}, need: []string{"apply", "conf", "restore", "snap", "restart"}},
}

func TestModes(t *testing.T) {
	for _, f := range families {
		t.Run(f.name, func(t *testing.T) { runFamily(t, f) })
	}
}

// TestE1Reproducer (E1=1): AsyncStorageWrites with vote requests sent at once (raft as forked: it
// lacks their E1 patch), the hold of rawnode off. The binding rejects such a stream at a vote
// request sent before its write; the test reports how many were.
func TestE1Reproducer(t *testing.T) {
	if os.Getenv("E1") == "" {
		t.Skip("E1=1 to run")
	}
	runFamily(t, family{name: "e1", scope: FullScope(), fix: func(m *Mode) {
		m.Async, m.Restarts, m.Snapshots, m.ConfChanges = true, true, false, false
	}, cfg: func(c *Config) { c.NoHoldVote = true }, expectRejects: true})
}

// TestSplitOrders (SPLIT=1): the two write orders DrawMode never draws (driver.go, splitNone's
// comment): HardState then entries, and raft's README order, entries then HardState (with
// restarts). The test reports how many streams the model rejects.
func TestSplitOrders(t *testing.T) {
	if os.Getenv("SPLIT") == "" {
		t.Skip("SPLIT=1 to run")
	}
	for _, sp := range []uint64{splitHardStateEntries, splitEntriesHardState} {
		split := sp
		runFamily(t, family{name: fmt.Sprintf("split%d", split), scope: FullScope(), fix: func(m *Mode) {
			syncOnly(m)
			m.Split, m.Restarts = split, true
		}, expectRejects: true})
	}
}

func modeFlags(m Mode) []string {
	var out []string
	add := func(b bool, s string) {
		if b {
			out = append(out, s)
		}
	}
	out = append(out, fmt.Sprintf("nodes=%d", m.Nodes), fmt.Sprintf("voters=%d", m.Voters),
		fmt.Sprintf("inflight=%d", m.MaxInflightMsgs), fmt.Sprintf("size=%d", m.MaxSizePerMsg),
		fmt.Sprintf("split=%d", m.Split), fmt.Sprintf("deliveries=%d", m.MaxDeliveries))
	add(m.Boot, "boot")
	add(m.PreVote, "prevote")
	add(m.CheckQuorum, "checkquorum")
	add(m.StepDownOnRemoval, "stepdown")
	add(m.Async, "async")
	add(m.Batch, "batch")
	add(m.Parallel, "parallel")
	add(m.Reads, "reads")
	add(m.Transfer, "transfer")
	add(m.ConfChanges, "member")
	add(m.Snapshots, "snap")
	add(m.SnapStatus, "snapstatus")
	add(m.Restarts, "restarts")
	add(m.Forward, "forward")
	return out
}

func runFamily(t *testing.T, f family) {
	n := runs(t)
	keep, rejects := os.Getenv("KEEP"), os.Getenv("REJECTS")
	accepted := 0
	reached := map[string]int{}
	perFlag := map[string][2]int{} // flag -> {accepted, runs}
	for k := 1; k <= n; k++ {
		m := DrawMode(f.scope)
		f.fix(&m)
		cfg := DefaultConfig()
		if f.cfg != nil {
			f.cfg(&cfg)
		}
		c := RunCluster(cfg, m)
		evs := c.Events()
		v := check.Check(c.CheckConfig(), evs)
		ok := v.Kind == check.Accepted
		flags := modeFlags(m)
		for _, fl := range flags {
			p := perFlag[fl]
			p[1]++
			if ok {
				p[0]++
			}
			perFlag[fl] = p
		}
		if keep != "" || (!ok && rejects != "") {
			dir := keep
			if !ok && rejects != "" {
				dir = rejects
			}
			base := filepath.Join(dir, fmt.Sprintf("%s-%d", f.name, k))
			fh, err := os.Create(base + ".ndjson")
			if err != nil {
				t.Fatal(err)
			}
			if err := ndjson.Write(fh, evs); err != nil {
				t.Fatal(err)
			}
			fh.Close()
			if err := os.WriteFile(base+".mode", []byte(fmt.Sprintf("%+v\n%v\n%v\n", m, flags, v)), 0o644); err != nil {
				t.Fatal(err)
			}
		}
		s := summarize(evs, m)
		if !ok {
			msg := fmt.Sprintf("run %d (%v): %v (%d events; event %s)", k, flags, v, len(evs), eventAt(evs, v.K))
			if f.expectRejects {
				t.Log(msg)
			} else {
				t.Error(msg)
			}
			continue
		}
		accepted++
		for p, c := range s.paths {
			if c > 0 {
				reached[p]++
			}
		}
	}
	for _, p := range f.need {
		if reached[p] == 0 {
			t.Errorf("%s: no accepted run reached %q", f.name, p)
		}
	}
	var keys []string
	for fl := range perFlag {
		keys = append(keys, fl)
	}
	sort.Strings(keys)
	for _, fl := range keys {
		t.Logf("%s: %-14s %d/%d accepted", f.name, fl, perFlag[fl][0], perFlag[fl][1])
	}
	t.Logf("%s: %d of %d accepted; runs reaching each path: %v", f.name, accepted, n, reached)
}

func eventAt(evs []*check.Event, k int) string {
	if k < 1 || k > len(evs) {
		return "-"
	}
	ev := evs[k-1]
	return fmt.Sprintf("%d %s %s", k, ev.E, ev.Node)
}

// summary is what a stream shows of a run: per path, how many times it was reached.
type summary struct {
	paths map[string]int
}

func summarize(evs []*check.Event, m Mode) summary {
	s := summary{paths: map[string]int{}}
	boots := 0
	leaders := map[int]bool{}
	for _, ev := range evs {
		switch ev.E {
		case "boot":
			boots++
		case "ready", "mem":
			if ev.Role == "leader" {
				leaders[ev.Term] = true
			}
		case "apply", "read", "conf", "restore", "snap":
			s.paths[ev.E]++
		}
	}
	if boots > int(m.Nodes) {
		s.paths["restart"] = boots - int(m.Nodes)
	}
	if len(leaders) > 1 {
		s.paths["leaderChange"] = len(leaders)
	}
	if m.Async && s.paths["apply"] > 0 {
		s.paths["async"] = 1
	}
	if m.Batch && s.paths["apply"] > 0 {
		s.paths["batch"] = 1
	}
	return s
}
