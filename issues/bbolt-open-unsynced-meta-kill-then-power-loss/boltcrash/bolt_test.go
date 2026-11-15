// Package boltcrash checks bbolt's crash images, with etcd's options: a child process commits
// random transactions under the ptrace recorder (crashsim), and every crash image built from the trace must open to the state of the last returned commit or of
// the one in flight (BoltImg), pass tx.Check, and keep working (more commits, reopen, Check).
//
// Experiment A: one incarnation per recording, chains of incarnations over the images.
// Experiment B: a kill -9 at a sync (the page cache survives), a restart in the same directory,
// then a power loss: the kill's unsynced writes are still unsynced.
//
// Each test fails if an image violates.
package boltcrash

import (
	"bytes"
	"encoding/binary"
	"flag"
	"fmt"
	"math/rand"
	"os"
	"os/exec"
	"path/filepath"
	"sort"
	"strconv"
	"strings"
	"testing"
	"time"

	bolt "go.etcd.io/bbolt"

	"boltfix/crashsim"
)

var (
	flagChains   = flag.Int("chains", 20, "chains (A) / runs (B)")
	flagIncs     = flag.Int("incs", 5, "incarnations per chain")
	flagImages   = flag.Int("images", 40, "images checked per recording")
	flagCommits  = flag.Int("commits", 25, "commits per incarnation")
	flagSeed     = flag.Int64("seed", 1, "base seed")
	flagScratch  = flag.String("scratch", os.TempDir(), "scratch dir")
	flagKeep     = flag.Bool("keep", false, "keep violation images")
	flagOpenSync = flag.Bool("opensync", false, "the child fdatasyncs the db right after Open (the candidate fix)")
	flagFN       = flag.Bool("fn", false, "the child fsyncs db's directory after Open (F-N)")
)

func TestMain(m *testing.M) {
	if os.Getenv("BOLTCRASH_CHILD") != "" {
		if err := childMain(); err != nil {
			fmt.Fprintln(os.Stderr, "child:", err)
			os.Exit(3)
		}
		os.Exit(0)
	}
	os.Exit(m.Run())
}

// ---- the workload ----

type state map[string]string // "bucket/key" -> value

func (s state) clone() state {
	t := state{}
	for k, v := range s {
		t[k] = v
	}
	return t
}

func (s state) equal(t state) bool {
	if len(s) != len(t) {
		return false
	}
	for k, v := range s {
		if w, ok := t[k]; !ok || w != v {
			return false
		}
	}
	return true
}

type op struct {
	del      bool
	bkt, key string
	val      string
}

func val(r *rand.Rand, tag string) string {
	var n int
	switch x := r.Intn(100); {
	case x < 88:
		n = 10 + r.Intn(500)
	case x < 97:
		n = 1000 + r.Intn(5000)
	default:
		n = 20000 + r.Intn(40000)
	}
	b := make([]byte, n)
	for i := range b {
		b[i] = byte('a' + r.Intn(26))
	}
	copy(b, tag)
	return string(b)
}

func opsOf(seed int64, inc, i int) []op {
	r := rand.New(rand.NewSource(seed*1_000_003 + int64(inc)*10_007 + int64(i)))
	n := 1 + r.Intn(30)
	out := make([]op, 0, n)
	for j := 0; j < n; j++ {
		b := []string{"a", "b"}[r.Intn(2)]
		k := fmt.Sprintf("k%03d", r.Intn(300))
		if r.Intn(4) == 0 {
			out = append(out, op{del: true, bkt: b, key: k})
		} else {
			out = append(out, op{bkt: b, key: k, val: val(r, fmt.Sprintf("%d.%d.%d.%d|", seed, inc, i, j))})
		}
	}
	return out
}

func apply(s state, ops []op) state {
	t := s.clone()
	for _, o := range ops {
		if o.del {
			delete(t, o.bkt+"/"+o.key)
		} else {
			t[o.bkt+"/"+o.key] = o.val
		}
	}
	return t
}

func boltOpts(seed int64) *bolt.Options {
	o := &bolt.Options{InitialMmapSize: 1 << 20}
	if seed%2 == 0 {
		o.FreelistType = bolt.FreelistMapType
	} else {
		o.FreelistType = bolt.FreelistArrayType
	}
	return o
}

// ---- the child ----

func childMain() error {
	root := os.Getenv("BC_ROOT")
	marker := os.Getenv("BC_MARKER")
	seed, _ := strconv.ParseInt(os.Getenv("BC_SEED"), 10, 64)
	inc, _ := strconv.Atoi(os.Getenv("BC_INC"))
	n, _ := strconv.Atoi(os.Getenv("BC_N"))
	mf, err := os.OpenFile(marker, os.O_WRONLY|os.O_APPEND|os.O_CREATE, 0o600)
	if err != nil {
		return err
	}
	mark := func(s string) { mf.Write([]byte(s)) }
	db, err := bolt.Open(filepath.Join(root, "db"), 0o600, boltOpts(seed))
	if err != nil {
		return err
	}
	if os.Getenv("BC_OPENSYNC") != "" {
		// the candidate fix: Open makes the state it read durable before the first write
		if err := db.Sync(); err != nil {
			return err
		}
	}
	if os.Getenv("BC_FN") != "" {
		// F-N: make db's directory entry durable (the fork fix C0b proposes for member/snap)
		d, err := os.Open(root)
		if err != nil {
			return err
		}
		if err := d.Sync(); err != nil {
			return err
		}
		d.Close()
	}
	tx, err := db.Begin(false)
	if err != nil {
		return err
	}
	mark(fmt.Sprintf("O %d", tx.ID()))
	tx.Rollback()
	for i := 1; i <= n; i++ {
		ops := opsOf(seed, inc, i)
		mark(fmt.Sprintf("B %d", i))
		var txid int
		err := db.Update(func(tx *bolt.Tx) error {
			txid = tx.ID()
			for _, o := range ops {
				b, err := tx.CreateBucketIfNotExists([]byte(o.bkt))
				if err != nil {
					return err
				}
				if o.del {
					if err := b.Delete([]byte(o.key)); err != nil {
						return err
					}
				} else if err := b.Put([]byte(o.key), []byte(o.val)); err != nil {
					return err
				}
			}
			return nil
		})
		if err != nil {
			return err
		}
		mark(fmt.Sprintf("C %d %d", i, txid))
	}
	return db.Close()
}

// ---- the driver ----

type run struct {
	events []crashsim.Event
	// per marker kind: event time
	begins  map[int]int // commit i -> time of its "B"
	commits map[int]int // commit i -> time of its "C"
	txids   map[int]int // commit i -> txid
	openTx  int
	nC      int
}

func parseRun(evs []crashsim.Event, base int) run {
	r := run{begins: map[int]int{}, commits: map[int]int{}, txids: map[int]int{}, openTx: -1}
	for t, e := range evs {
		if t < base || e.Kind != crashsim.KMarker {
			continue
		}
		f := strings.Fields(e.Marker)
		switch f[0] {
		case "O":
			r.openTx, _ = strconv.Atoi(f[1])
		case "B":
			i, _ := strconv.Atoi(f[1])
			r.begins[i] = t
		case "C":
			i, _ := strconv.Atoi(f[1])
			x, _ := strconv.Atoi(f[2])
			r.commits[i] = t
			r.txids[i] = x
			if i > r.nC {
				r.nC = i
			}
		}
	}
	return r
}

func record(t *testing.T, root, marker string, seed int64, inc, n, killAt int) ([]crashsim.Event, bool) {
	cmd := exec.Command(os.Args[0])
	cmd.Env = append(os.Environ(), "BOLTCRASH_CHILD=1", "BC_ROOT="+root, "BC_MARKER="+marker,
		fmt.Sprintf("BC_SEED=%d", seed), fmt.Sprintf("BC_INC=%d", inc), fmt.Sprintf("BC_N=%d", n))
	if *flagFN {
		cmd.Env = append(cmd.Env, "BC_FN=1")
	}
	if *flagOpenSync {
		cmd.Env = append(cmd.Env, "BC_OPENSYNC=1")
	}
	cmd.Stderr = os.Stderr
	evs, killed, err := crashsim.RecordKill(root, marker, cmd, killAt)
	if err != nil {
		t.Fatalf("record: %v", err)
	}
	return evs, killed
}

// readImage opens the image (write mode, as etcd), reads both buckets and runs Check.
func readImage(dir string, seed int64) (state, int, error) {
	type res struct {
		s    state
		txid int
		err  error
	}
	ch := make(chan res, 1)
	go func() {
		var r res
		defer func() {
			if p := recover(); p != nil {
				r.s, r.err = nil, fmt.Errorf("panic: %v", p)
			}
			ch <- r
		}()
		r.s, r.txid, r.err = readImage1(dir, seed)
	}()
	select {
	case r := <-ch:
		return r.s, r.txid, r.err
	case <-time.After(20 * time.Second):
		return nil, 0, fmt.Errorf("hang: reading the image did not finish in 20s (a cycle in the corrupted tree)")
	}
}

func readImage1(dir string, seed int64) (state, int, error) {
	db, err := bolt.Open(filepath.Join(dir, "db"), 0o600, boltOpts(seed))
	if err != nil {
		return nil, 0, fmt.Errorf("open: %w", err)
	}
	defer db.Close()
	s := state{}
	var txid int
	err = db.View(func(tx *bolt.Tx) error {
		txid = tx.ID()
		for _, bn := range []string{"a", "b"} {
			b := tx.Bucket([]byte(bn))
			if b == nil {
				continue
			}
			if err := b.ForEach(func(k, v []byte) error {
				s[bn+"/"+string(k)] = string(v)
				return nil
			}); err != nil {
				return err
			}
		}
		var errs []string
		for e := range tx.Check() {
			errs = append(errs, e.Error())
		}
		if len(errs) > 0 {
			return fmt.Errorf("check: %s", strings.Join(errs, "; "))
		}
		return nil
	})
	return s, txid, err
}

// stress: more commits on a copy of the image, reopen, Check (freelist/page sanity after recovery).
func stress(dir string, seed int64) (err error) {
	defer func() {
		if p := recover(); p != nil {
			err = fmt.Errorf("panic: %v", p)
		}
	}()
	db, err := bolt.Open(filepath.Join(dir, "db"), 0o600, boltOpts(seed))
	if err != nil {
		return err
	}
	exp, _, err := func() (state, int, error) { db.Close(); return readImage(dir, seed) }()
	if err != nil {
		return err
	}
	db, err = bolt.Open(filepath.Join(dir, "db"), 0o600, boltOpts(seed))
	if err != nil {
		return err
	}
	for i := 1; i <= 8; i++ {
		ops := opsOf(seed+7777, 99, i)
		exp = apply(exp, ops)
		if err := db.Update(func(tx *bolt.Tx) error {
			for _, o := range ops {
				b, err := tx.CreateBucketIfNotExists([]byte(o.bkt))
				if err != nil {
					return err
				}
				if o.del {
					b.Delete([]byte(o.key))
				} else if err := b.Put([]byte(o.key), []byte(o.val)); err != nil {
					return err
				}
			}
			return nil
		}); err != nil {
			db.Close()
			return err
		}
	}
	db.Close()
	got, _, err := readImage(dir, seed)
	if err != nil {
		return fmt.Errorf("after stress: %w", err)
	}
	if !got.equal(exp) {
		return fmt.Errorf("after stress: state differs")
	}
	return nil
}

func copyDir(src, dst string) error {
	return exec.Command("cp", "-a", src+"/.", dst).Run()
}

func describe(s state, cands map[string]state) string {
	var names []string
	for n, c := range cands {
		if c.equal(s) {
			names = append(names, n)
		}
	}
	sort.Strings(names)
	return strings.Join(names, ",")
}

type tally struct {
	images, ok, inflight, violations int
	kinds                            map[string]int
}

func (tl *tally) violation(t *testing.T, kind, detail string, keep func() string) {
	tl.violations++
	if tl.kinds == nil {
		tl.kinds = map[string]int{}
	}
	tl.kinds[kind]++
	where := ""
	if *flagKeep && keep != nil {
		where = " kept " + keep()
	}
	t.Logf("VIOLATION %s: %s%s", kind, detail, where)
}

func newModel(t *testing.T, root string) *crashsim.Model {
	m, err := crashsim.Scan(root, false)
	if err != nil {
		t.Fatal(err)
	}
	return m
}

var models = []string{crashsim.Posix, crashsim.Ordered, crashsim.Kill}

// TestBoltChains is experiment A.
func TestBoltChains(t *testing.T) {
	os.MkdirAll(*flagScratch, 0o755)
	var tl tally
	for c := 0; c < *flagChains; c++ {
		seed := *flagSeed*1000 + int64(c)
		work, _ := os.MkdirTemp(*flagScratch, "a-")
		cur := filepath.Join(work, "cur")
		os.Mkdir(cur, 0o755)
		start := state{}
		for inc := 0; inc < *flagIncs; inc++ {
			root := filepath.Join(work, fmt.Sprintf("rec%d", inc))
			os.Mkdir(root, 0o755)
			copyDir(cur, root)
			marker := filepath.Join(work, fmt.Sprintf("marker%d", inc))
			m := newModel(t, root)
			evs, _ := record(t, root, marker, seed, inc, *flagCommits, -1)
			m.SetEvents(evs)
			r := parseRun(evs, 0)
			states := []state{start}
			for i := 1; i <= *flagCommits; i++ {
				states = append(states, apply(states[i-1], opsOf(seed, inc, i)))
			}
			rng := rand.New(rand.NewSource(seed*31 + int64(inc)))
			var next string
			for img := 0; img < *flagImages; img++ {
				K := rng.Intn(len(evs) + 1)
				if img == 0 {
					K = len(evs) // the graceful end
				}
				spec := crashsim.Spec{K: K, Model: models[rng.Intn(len(models))], Seed: rng.Int63()}
				dst := filepath.Join(work, fmt.Sprintf("img%d-%d", inc, img))
				os.Mkdir(dst, 0o755)
				if err := m.Build(spec, dst); err != nil {
					t.Fatalf("build: %v", err)
				}
				tl.images++
				// j: commits returned before K; in flight: j+1 if it began before K
				j := 0
				for i := 1; i <= *flagCommits; i++ {
					if ct, ok := r.commits[i]; ok && ct < K {
						j = i
					}
				}
				inflight := false
				if bt, ok := r.begins[j+1]; ok && bt < K {
					inflight = true
				}
				detail := fmt.Sprintf("chain %d seed %d inc %d %s j=%d inflight=%v", c, seed, inc, spec, j, inflight)
				keep := func() string { return dst }
				if _, err := os.Stat(filepath.Join(dst, "db")); err != nil {
					if inc == 0 && j == 0 {
						// the first Open's create was not made durable: an empty directory is the
						// state before the first start (no commit returned yet)
						tl.ok++
						if img == 0 {
							t.Fatalf("graceful image has no db")
						}
						continue
					}
					tl.violation(t, "db file missing", detail, keep)
					continue
				}
				got, _, err := readImage(dst, seed)
				if err != nil {
					if inc == 0 && j == 0 {
						tl.violation(t, "first start: open/check error before any commit returned: "+err.Error(), detail, keep)
					} else {
						tl.violation(t, "open/check error: "+err.Error(), detail, keep)
					}
					continue
				}
				switch {
				case got.equal(states[j]):
					tl.ok++
				case inflight && got.equal(states[j+1]):
					tl.ok++
					tl.inflight++
				default:
					tl.violation(t, "state is neither the last returned nor the in-flight commit", detail, keep)
					continue
				}
				sc := dst + "-stress"
				os.Mkdir(sc, 0o755)
				copyDir(dst, sc)
				if err := stress(sc, seed); err != nil {
					tl.violation(t, "stress after recovery: "+err.Error(), detail, keep)
				}
				os.RemoveAll(sc)
				if img == 1 || (next == "" && img == *flagImages-1) {
					next = dst
				}
			}
			if next == "" {
				t.Fatalf("no image to continue from")
			}
			got, _, err := readImage(next, seed)
			if err != nil {
				got = state{} // missing db at first start
			}
			start = got
			os.RemoveAll(cur)
			os.Mkdir(cur, 0o755)
			copyDir(next, cur)
			if !*flagKeep || tl.violations == 0 {
				for img := 0; img < *flagImages; img++ {
					os.RemoveAll(filepath.Join(work, fmt.Sprintf("img%d-%d", inc, img)))
				}
			}
			os.RemoveAll(root)
		}
		if tl.violations == 0 {
			os.RemoveAll(work)
		}
	}
	t.Logf("A: images %d ok %d (in-flight %d) violations %d %v", tl.images, tl.ok, tl.inflight, tl.violations, tl.kinds)
	if tl.violations > 0 {
		t.Errorf("%d of %d crash images violate", tl.violations, tl.images)
	}
}

// TestBoltKillThenPower is experiment B: inc 1 killed at a sync, inc 2 restarted in the same
// directory (it sees the page cache), then a power loss during inc 2.
func TestBoltKillThenPower(t *testing.T) {
	os.MkdirAll(*flagScratch, 0o755)
	var tl tally
	for c := 0; c < *flagChains; c++ {
		seed := *flagSeed*1000 + int64(c)
		work, _ := os.MkdirTemp(*flagScratch, "b-")
		root := filepath.Join(work, "root")
		os.Mkdir(root, 0o755)
		// inc 0: a few clean commits, then the state is taken as durable
		marker0 := filepath.Join(work, "marker0")
		evs0, _ := record(t, root, marker0, seed, 0, 10, -1)
		s0 := state{}
		for i := 1; i <= 10; i++ {
			s0 = apply(s0, opsOf(seed, 0, i))
		}
		_ = evs0
		m := newModel(t, root)
		rng := rand.New(rand.NewSource(seed * 17))
		// inc 1: killed at a sync
		killAt := 2 + rng.Intn(2*(*flagCommits))
		marker1 := filepath.Join(work, "marker1")
		evs1, killed := record(t, root, marker1, seed, 1, *flagCommits, killAt)
		if !killed {
			os.RemoveAll(work)
			continue
		}
		r1 := parseRun(evs1, 0)
		st1 := []state{s0}
		for i := 1; i <= *flagCommits; i++ {
			st1 = append(st1, apply(st1[i-1], opsOf(seed, 1, i)))
		}
		// inc 2: restart in place
		marker2 := filepath.Join(work, "marker2")
		evs2, _ := record(t, root, marker2, seed, 2, *flagCommits, -1)
		r2 := parseRun(evs2, 0)
		// which state did inc 2 open? by txid
		j1 := r1.nC
		var vis state
		switch {
		case r2.openTx == r1.txids[j1] || (j1 == 0 && r2.openTx == r1.openTx):
			vis = st1[j1]
		case r2.openTx == r1.txids[j1]+1 || (j1 == 0 && r2.openTx == r1.openTx+1):
			vis = st1[j1+1] // the killed commit's meta was in the page cache
		default:
			t.Fatalf("inc 2 opened txid %d; inc 1 committed %d (txid %d)", r2.openTx, j1, r1.txids[j1])
		}
		st2 := []state{vis}
		for i := 1; i <= *flagCommits; i++ {
			st2 = append(st2, apply(st2[i-1], opsOf(seed, 2, i)))
		}
		all := append(append([]crashsim.Event{}, evs1...), evs2...)
		m.SetEvents(all)
		base := len(evs1)
		// the first sync of inc 2 (a data fdatasync)
		firstSync := len(all)
		for k := base; k < len(all); k++ {
			if all[k].Kind == crashsim.KSync {
				firstSync = k
				break
			}
		}
		for img := 0; img < *flagImages; img++ {
			var K int
			if img%2 == 0 && firstSync > base {
				K = base + rng.Intn(firstSync-base+1) // before inc 2's first sync returns
			} else {
				K = base + rng.Intn(len(all)-base+1)
			}
			spec := crashsim.Spec{K: K, Model: []string{crashsim.Posix, crashsim.Ordered}[rng.Intn(2)], Seed: rng.Int63()}
			dst := filepath.Join(work, fmt.Sprintf("img%d", img))
			os.Mkdir(dst, 0o755)
			if err := m.Build(spec, dst); err != nil {
				t.Fatalf("build: %v", err)
			}
			tl.images++
			j := 0
			for i := 1; i <= *flagCommits; i++ {
				if ct, ok := r2.commits[i]; ok && ct+base < K {
					j = i
				}
			}
			cands := map[string]state{}
			if j == 0 {
				cands["L"] = st1[j1]
				cands["F"] = st1[j1+min(1, *flagCommits-j1)]
			}
			cands[fmt.Sprintf("G%d", j)] = st2[j]
			if j < *flagCommits {
				cands[fmt.Sprintf("G%d(in flight)", j+1)] = st2[j+1]
			}
			detail := fmt.Sprintf("run %d seed %d killAt %d (inc1 commits %d, inc2 saw %s) %s j=%d", c, seed, killAt, j1,
				map[bool]string{true: "F", false: "L"}[!vis.equal(st1[j1])], spec, j)
			keep := func() string { return dst }
			got, _, err := readImage(dst, seed)
			if err != nil {
				tl.violation(t, "open/check error: "+err.Error(), detail, keep)
				continue
			}
			if d := describe(got, cands); d != "" {
				tl.ok++
				if !*flagKeep {
					os.RemoveAll(dst)
				}
				continue
			}
			tl.violation(t, "state is none of L, F, inc 2's commits", detail, keep)
		}
		if tl.violations == 0 {
			os.RemoveAll(work)
		}
	}
	t.Logf("B: images %d ok %d violations %d %v", tl.images, tl.ok, tl.violations, tl.kinds)
	if tl.violations > 0 {
		t.Errorf("%d of %d crash images violate", tl.violations, tl.images)
	}
}

var _ = bytes.Equal
var _ = binary.BigEndian
