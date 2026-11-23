package check_test

// The differential test: Check against TLC (streamcheck.py), on the verdicts testdata/
// gen-fixtures.sh recorded (testdata/verdicts.txt): Antithesis's recorded streams, the mutations
// of their scripts/mutate.py (cut after the event TLC stops at), and simulator streams of several
// modes; and (testdata/verdicts-fuzz.txt, testdata/gen-fuzz.py) random perturbations of the
// recorded streams. EXTRA_VERDICTS=<file> checks another verdicts file of the same format (paths relative
// to it), e.g. a larger simulator batch.

import (
	"bufio"
	"compress/gzip"
	"os"
	"path/filepath"
	"sort"
	"strconv"
	"strings"
	"testing"

	"github.com/mit-pdos/etcd-grove/examples/raft/antithesis/check"
	"github.com/mit-pdos/etcd-grove/examples/raft/antithesis/check/ndjson"
)

func servers(n int) check.Set {
	var s check.Set
	for i := 1; i <= n; i++ {
		s = check.SetAdd(s, "raft"+strconv.Itoa(i))
	}
	return s
}

// configs are antithesis-fm/spec/EtcdBinding*.cfg.
var configs = map[string]*check.Config{
	"EtcdBinding.cfg":       {Server: servers(3), InitVoters: servers(3), Bootstrapped: true},
	"EtcdBindingEmpty.cfg":  {Server: servers(3), InitVoters: servers(3), Bootstrapped: false},
	"EtcdBinding5.cfg":      {Server: servers(5), InitVoters: servers(5), Bootstrapped: true},
	"EtcdBinding5Empty.cfg": {Server: servers(5), InitVoters: servers(5), Bootstrapped: false},
	"EtcdBindingM.cfg":      {Server: servers(5), InitVoters: servers(3), Bootstrapped: true},
	"EtcdBindingMEmpty.cfg": {Server: servers(5), InitVoters: servers(3), Bootstrapped: false},
}

type fixture struct {
	source, file, cfg string
	at                int
	tlc               string // streamcheck.py's line
}

func readVerdicts(t *testing.T, path string) []fixture {
	f, err := os.Open(path)
	if os.IsNotExist(err) && strings.HasSuffix(path, "verdicts-fuzz.txt") {
		return nil
	}
	if err != nil {
		t.Fatal(err)
	}
	defer f.Close()
	var out []fixture
	sc := bufio.NewScanner(f)
	sc.Buffer(make([]byte, 1<<20), 1<<20)
	for sc.Scan() {
		fs := strings.SplitN(sc.Text(), " ", 5)
		if len(fs) < 5 {
			continue
		}
		at, _ := strconv.Atoi(fs[3])
		out = append(out, fixture{source: fs[0], file: filepath.Join(filepath.Dir(path), fs[1]), cfg: fs[2], at: at, tlc: fs[4]})
	}
	return out
}

func readStream(t *testing.T, path string) []*check.Event {
	f, err := os.Open(path)
	if err != nil {
		t.Fatal(err)
	}
	defer f.Close()
	z, err := gzip.NewReader(f)
	if err != nil {
		t.Fatal(err)
	}
	evs, err := ndjson.Read(z)
	if err != nil {
		t.Fatalf("%s: %v", path, err)
	}
	return evs
}

// agrees: the same kind of verdict at the same event, and for a violation the same properties.
func agrees(v check.Verdict, tlc string) bool {
	fs := strings.Fields(tlc)
	if len(fs) == 0 {
		return false
	}
	switch fs[0] {
	case "ACCEPTED", "REJECTED":
		k, _ := strconv.Atoi(fs[1])
		want := check.Accepted
		if fs[0] == "REJECTED" {
			want = check.Rejected
		}
		return v.Kind == want && v.K == k
	case "VIOLATED":
		k, _ := strconv.Atoi(fs[1])
		names := strings.Split(fs[2], ",")
		got := append([]string(nil), v.Names...)
		sort.Strings(names)
		sort.Strings(got)
		return v.Kind == check.Violated && v.K == k && strings.Join(names, ",") == strings.Join(got, ",")
	case "ERROR":
		return v.Kind == check.Error
	}
	return false
}

func runFixtures(t *testing.T, fx []fixture) {
	type tally struct{ agree, disagree int }
	counts := map[string]*tally{}
	for _, f := range fx {
		cfg := configs[f.cfg]
		if cfg == nil {
			t.Fatalf("%s: unknown configuration %s", f.file, f.cfg)
		}
		if counts[f.source] == nil {
			counts[f.source] = &tally{}
		}
		v := check.Check(cfg, readStream(t, f.file))
		if agrees(v, f.tlc) {
			counts[f.source].agree++
			if f.source == "mutation" && v.K < f.at {
				t.Errorf("%s: rejected at %d, before the mutated event %d", f.file, v.K, f.at)
			}
		} else {
			counts[f.source].disagree++
			tlc := f.tlc
			if len(tlc) > 160 {
				tlc = tlc[:160]
			}
			t.Errorf("%s (%s): Go %v, TLC %s", filepath.Base(f.file), f.cfg, v, tlc)
		}
	}
	var srcs []string
	for s := range counts {
		srcs = append(srcs, s)
	}
	sort.Strings(srcs)
	for _, s := range srcs {
		t.Logf("%-9s agree %4d  disagree %d", s, counts[s].agree, counts[s].disagree)
	}
}

func TestDifferential(t *testing.T) {
	fx := readVerdicts(t, "testdata/verdicts.txt")
	fx = append(fx, readVerdicts(t, "testdata/verdicts-fuzz.txt")...)
	runFixtures(t, fx)
}

func TestDifferentialExtra(t *testing.T) {
	p := os.Getenv("EXTRA_VERDICTS")
	if p == "" {
		t.Skip("EXTRA_VERDICTS not set")
	}
	runFixtures(t, readVerdicts(t, p))
}
