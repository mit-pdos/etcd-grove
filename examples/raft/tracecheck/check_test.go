//go:build with_tla

package tracecheck

import (
	"bytes"
	"encoding/json"
	"fmt"
	"math/rand/v2"
	"os"
	"os/exec"
	"path/filepath"
	"regexp"
	"strconv"
	"strings"
	"sync"
	"testing"

	"github.com/anishathalye/porcupine"
	"github.com/mit-pdos/etcd-grove/examples/raft/tracecheck/etcdraft"
	"github.com/mit-pdos/etcd-grove/examples/raft/tracecheck/etcdraft/ndjson"
	"github.com/mit-pdos/etcd-grove/examples/raft/tracecheck/etcdraft/pmodel"
)

func envInt(name string, def int) int {
	if n, err := strconv.Atoi(os.Getenv(name)); err == nil && n > 0 {
		return n
	}
	return def
}

// traceNDJSON runs a seed's cluster and returns its trace as NDJSON.
func traceNDJSON(t *testing.T, cfg Config) []byte {
	s, err := New(cfg)
	if err != nil {
		t.Fatal(err)
	}
	if err := s.Run(); err != nil {
		t.Fatalf("seed %d: %v", cfg.Seed, err)
	}
	var buf bytes.Buffer
	if err := WriteNDJSON(&buf, s.Events()); err != nil {
		t.Fatal(err)
	}
	return buf.Bytes()
}

// goVerdicts checks an NDJSON trace with the direct checker and with porcupine.
func goVerdicts(t *testing.T, nd []byte) (direct etcdraft.Result, pc porcupine.CheckResult, err error) {
	events, err := ndjson.ReadNDJSON(bytes.NewReader(nd))
	if err != nil {
		return direct, pc, err
	}
	tr, err := etcdraft.NewTrace(events)
	if err != nil {
		return direct, pc, err
	}
	return etcdraft.CheckTrace(tr, true), pmodel.CheckPorcupine(tr, true, 0), nil
}

// TestTracesCheck: the traces of seeds 1..TRACE_SEEDS (default 20) are matched by the Go
// transcription of the trace specification, by the direct checker and by porcupine.
func TestTracesCheck(t *testing.T) {
	for seed := uint64(1); seed <= uint64(envInt("TRACE_SEEDS", 20)); seed++ {
		nd := traceNDJSON(t, DefaultConfig(seed))
		r, pc, err := goVerdicts(t, nd)
		if err != nil {
			t.Fatalf("seed %d: %v", seed, err)
		}
		if !r.TLCOK() || pc != porcupine.Ok {
			t.Errorf("seed %d: direct %v, porcupine %v", seed, r, pc)
		}
	}
}

// mutate returns a copy of the NDJSON trace with one random change, and a description: a logged
// value of a line changed, a line deleted, or two adjacent lines swapped.
func mutate(rng *rand.Rand, nd []byte) ([]byte, string) {
	lines := strings.Split(strings.TrimSpace(string(nd)), "\n")
	k := rng.IntN(len(lines))
	switch rng.IntN(10) {
	case 0:
		desc := fmt.Sprintf("delete line %d", k+1)
		return []byte(strings.Join(append(lines[:k:k], lines[k+1:]...), "\n") + "\n"), desc
	case 1:
		if k+1 < len(lines) {
			lines[k], lines[k+1] = lines[k+1], lines[k]
			return []byte(strings.Join(lines, "\n") + "\n"), fmt.Sprintf("swap lines %d, %d", k+1, k+2)
		}
	}
	var rec map[string]any
	if err := json.Unmarshal([]byte(lines[k]), &rec); err != nil {
		panic(err)
	}
	ev := rec["event"].(map[string]any)
	st := ev["state"].(map[string]any)
	type field struct {
		m   map[string]any
		key string
	}
	fields := []field{{st, "term"}, {st, "commit"}, {ev, "log"}, {st, "vote"}, {ev, "role"}}
	if msg, ok := ev["msg"].(map[string]any); ok {
		fields = append(fields, field{msg, "term"}, field{msg, "index"}, field{msg, "logTerm"},
			field{msg, "entries"}, field{msg, "commit"}, field{msg, "reject"}, field{msg, "to"})
	}
	f := fields[rng.IntN(len(fields))]
	switch v := f.m[f.key].(type) {
	case float64:
		if v > 0 && rng.IntN(2) == 0 {
			f.m[f.key] = v - 1
		} else {
			f.m[f.key] = v + 1
		}
	case bool:
		f.m[f.key] = !v
	case string:
		switch f.key {
		case "role":
			roles := []string{"StateFollower", "StateCandidate", "StateLeader"}
			f.m[f.key] = roles[(indexOf(roles, v)+1+rng.IntN(2))%3]
		default: // an id
			n, _ := strconv.Atoi(v)
			f.m[f.key] = strconv.Itoa((n + 1) % 4)
		}
	}
	b, err := json.Marshal(rec)
	if err != nil {
		panic(err)
	}
	lines[k] = string(b)
	return []byte(strings.Join(lines, "\n") + "\n"), fmt.Sprintf("line %d (%s): %s", k+1, ev["name"], f.key)
}

func indexOf(xs []string, x string) int {
	for k, y := range xs {
		if y == x {
			return k
		}
	}
	return 0
}

// tlcLine matches the trace position in a state of TLC's error trace.
var tlcLine = regexp.MustCompile(`/\\ l = (\d+)`)

// tlcAccepts runs TLC's trace validation on the file (as raft's tla/validate.sh does): whether
// TLC found no error, and otherwise the line at which its error trace stops (the last l), 0 if
// none.
func tlcAccepts(t *testing.T, tools, spec, file string) (bool, int) {
	meta := t.TempDir()
	cmd := exec.Command("java", "-XX:+UseParallelGC", "-cp",
		filepath.Join(tools, "tla2tools.jar")+":"+filepath.Join(tools, "CommunityModules-deps.jar"),
		"tlc2.TLC", "-config", "Traceetcdraft.cfg", "Traceetcdraft.tla", "-lncheck", "final",
		"-metadir", meta, "-fpmem", "0.1")
	cmd.Dir = spec
	cmd.Env = append(os.Environ(), "JSON="+file)
	out, _ := cmd.CombinedOutput()
	s := string(out)
	switch {
	case strings.Contains(s, "No error has been found"):
		return true, 0
	case strings.Contains(s, "TraceMatched was violated") || strings.Contains(s, "is violated") ||
		strings.Contains(s, "Error:"):
		line := 0
		if ms := tlcLine.FindAllStringSubmatch(s, -1); len(ms) > 0 {
			line, _ = strconv.Atoi(ms[len(ms)-1][1])
		}
		return false, line
	}
	t.Fatalf("TLC on %s: no verdict:\n%s", file, s)
	return false, 0
}

// TestAgainstTLC compares the verdicts of TLC (on raft's own Traceetcdraft.tla, with the
// transcriptions' one repair, repairedSpec) and of the Go transcription (the direct checker and
// porcupine) on the traces of seeds 1..TLC_SEEDS (default 3) and TLC_MUTANTS (default 10) mutants
// of each. It needs TLA_TOOLS, a directory with tla2tools.jar and CommunityModules-deps.jar, and
// TLA_SPEC, raft's tla/ directory (the pinned fork's); it is skipped without them.
func TestAgainstTLC(t *testing.T) {
	tools, spec := os.Getenv("TLA_TOOLS"), os.Getenv("TLA_SPEC")
	if tools == "" || spec == "" {
		t.Skip("TLA_TOOLS and TLA_SPEC not set")
	}
	spec = repairedSpec(t, spec)
	dir := t.TempDir()
	type job struct {
		name string
		nd   []byte
	}
	var jobs []job
	rng := rand.New(rand.NewPCG(1, 2))
	for seed := uint64(1); seed <= uint64(envInt("TLC_SEEDS", 3)); seed++ {
		nd := traceNDJSON(t, DefaultConfig(seed))
		jobs = append(jobs, job{fmt.Sprintf("seed %d", seed), nd})
		for k := 0; k < envInt("TLC_MUTANTS", 10); k++ {
			m, desc := mutate(rng, nd)
			jobs = append(jobs, job{fmt.Sprintf("seed %d, %s", seed, desc), m})
		}
		// FullConfig's traces (configuration changes, snapshots): the specification rejects
		// most of them (notes/raft-trace-validation.md, "Where etcdraft.tla does not fit
		// raft"), and the verdicts, and the line, must still agree.
		jobs = append(jobs, job{fmt.Sprintf("full seed %d", seed), traceNDJSON(t, FullConfig(seed))})
		// the concurrent harness's traces, both configurations
		cnd, _ := concurrentNDJSON(t, DefaultCConfig())
		jobs = append(jobs, job{fmt.Sprintf("concurrent seed %d", seed), cnd})
		cnd, _ = concurrentNDJSON(t, FullCConfig())
		jobs = append(jobs, job{fmt.Sprintf("concurrent full seed %d", seed), cnd})
	}
	sem := make(chan struct{}, envInt("TLC_PARALLEL", 4))
	var wg sync.WaitGroup
	var mu sync.Mutex
	agree, rejected := 0, 0
	for n, j := range jobs {
		wg.Add(1)
		go func() {
			defer wg.Done()
			sem <- struct{}{}
			defer func() { <-sem }()
			file := filepath.Join(dir, fmt.Sprintf("t%d.ndjson", n))
			if err := os.WriteFile(file, j.nd, 0o644); err != nil {
				t.Error(err)
				return
			}
			tlc, tlcAt := tlcAccepts(t, tools, spec, file)
			r, pc, err := goVerdicts(t, j.nd)
			// TLC's verdict is TLCOK (matched, and the search never branched); porcupine's is
			// OK (some path matches).
			goOK := err == nil && r.TLCOK()
			mu.Lock()
			defer mu.Unlock()
			if tlc != goOK || (err == nil && r.OK) != (pc == porcupine.Ok) {
				t.Errorf("%s: TLC %t, direct %v (err %v), porcupine %v", j.name, tlc, r, err, pc)
				return
			}
			// A trace TLC rejects: its error trace stops at the line no state steps through
			// (an invariant violation, which TLC reports at the violating state, is compared by
			// verdict only).
			if !tlc && err == nil && r.Violation == "" && r.EvalError == "" && r.Branched == 0 && tlcAt != 0 && tlcAt != r.Line {
				t.Errorf("%s: TLC stops at line %d, the direct checker at line %d", j.name, tlcAt, r.Line)
				return
			}
			agree++
			if !tlc {
				rejected++
			}
		}()
	}
	wg.Wait()
	t.Logf("%d traces, verdicts agree on %d (%d rejected by all three)", len(jobs), agree, rejected)
}

// leaderCompletenessGuard is the guard of upstream's LeaderCompletenessInv and its repair, the
// transcriptions' (issues/raft-tla-leader-completeness-stale-leader.md; notes/trace-validation-plan.md,
// Q4 (b)): the only place the transcriptions depart from raft's tla/.
const (
	leaderCompletenessGuard         = "                currentTerm[l] > entry.term =>"
	leaderCompletenessRepairedGuard = "                currentTerm[l] > entry.term /\\ currentTerm[l] >= currentTerm[i] =>"
)

// repairedSpec copies raft's tla/ directory to a temporary one with LeaderCompletenessInv's guard
// repaired, so that TLC checks what the transcriptions check.
func repairedSpec(t *testing.T, spec string) string {
	dir := t.TempDir()
	ents, err := os.ReadDir(spec)
	if err != nil {
		t.Fatal(err)
	}
	for _, e := range ents {
		if e.IsDir() {
			continue
		}
		b, err := os.ReadFile(filepath.Join(spec, e.Name()))
		if err != nil {
			t.Fatal(err)
		}
		if e.Name() == "etcdraft.tla" {
			s := string(b)
			if strings.Count(s, leaderCompletenessGuard) != 1 {
				t.Fatalf("%s: LeaderCompletenessInv's guard not found once", e.Name())
			}
			b = []byte(strings.Replace(s, leaderCompletenessGuard, leaderCompletenessRepairedGuard, 1))
		}
		if err := os.WriteFile(filepath.Join(dir, e.Name()), b, 0o644); err != nil {
			t.Fatal(err)
		}
	}
	return dir
}
