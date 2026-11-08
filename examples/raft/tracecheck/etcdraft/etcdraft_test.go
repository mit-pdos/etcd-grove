package etcdraft

import (
	"os"
	"testing"
)

// bounds are MCGo.tla's constants.
type bounds struct {
	maxTerm, maxLog, maxMsgs, maxReconfig int
}

// constraint is MCGo.tla's GoConstraint.
func (b bounds) constraint(s *State) bool {
	for _, i := range s.Server {
		if s.S[i].CurrentTerm > b.maxTerm || len(s.S[i].Log) > b.maxLog {
			return false
		}
	}
	n := 0
	for _, m := range s.Messages.Domain() {
		n += s.Messages.Count(m)
	}
	for _, m := range s.PendingMessages.Domain() {
		n += s.PendingMessages.Count(m)
	}
	return n <= b.maxMsgs && s.ReconfigCount <= b.maxReconfig
}

// explore is TLC's breadth-first search of `Init /\ [][NextDynamic]_vars` under the
// constraint: the number of distinct states found (TLC leaves a successor violating the
// constraint out: it is neither counted nor explored), and the first invariant violation.
func explore(t *testing.T, initServer, server Set, b bounds, limit int) (int, string) {
	init := Init(initServer, server)
	seen := map[string]bool{init.Key(): true}
	frontier := []*State{init}
	for len(frontier) > 0 {
		var next []*State
		for _, s := range frontier {
			for _, s2 := range s.NextDynamic() {
				k := s2.Key()
				if seen[k] || !b.constraint(s2) {
					continue
				}
				seen[k] = true
				if v := s2.Violated(); v != "" {
					return len(seen), v
				}
				next = append(next, s2)
			}
		}
		if len(seen) > limit {
			t.Fatalf("more than %d states", limit)
		}
		frontier = next
	}
	return len(seen), ""
}

// TestStateSpaceMatchesTLC compares the number of distinct states of the Go transcription's
// NextDynamic, under MCGo.tla's bounds, with TLC's on etcdraft.tla itself (MCGo-<name>.cfg, run
// by hand: the counts below are TLC's, 2026-11-08, tla2tools nightly, etcdraft.tla of the raft
// fork 565c2bd). Every action of the specification is in NextDynamic, so equal counts mean the two
// next-state relations agree on the states reachable within the bounds.
func TestStateSpaceMatchesTLC(t *testing.T) {
	for _, c := range []struct {
		name               string
		server, initServer Set
		b                  bounds
		tlc                int
		big                bool
	}{
		{"b", NewSet(1, 2), NewSet(1), bounds{1, 1, 2, 1}, 17930, false},
		{"d", NewSet(1, 2), NewSet(1, 2), bounds{1, 1, 2, 1}, 149307, false},
		{"e", NewSet(1, 2, 3), NewSet(1, 2), bounds{1, 1, 1, 1}, 25569, false},
		{"h", NewSet(1, 2), NewSet(1, 2), bounds{2, 1, 1, 0}, 330653, false},
	} {
		if c.big && os.Getenv("ETCDRAFT_BIG") == "" {
			continue
		}
		n, v := explore(t, c.initServer, c.server, c.b, 10*c.tlc)
		if v != "" {
			t.Errorf("%s: invariant %s violated", c.name, v)
		}
		if n != c.tlc {
			t.Errorf("%s: %d distinct states, TLC found %d", c.name, n, c.tlc)
		} else {
			t.Logf("%s: %d distinct states, as TLC", c.name, n)
		}
	}
}
