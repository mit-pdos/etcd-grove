// Differential fuzzer: bbolt v1.5.0 against the key-value model of the bbolt axioms
// (Spec/go_etcd_io/bbolt/*_kv.lean, InvBbolt.lean). Every operation respects the specs'
// premises; a panic, an unexpected error, a result the model excludes, or a retained slice
// whose bytes changed while its transaction is live (txBytes is persistent) is reported.
package main

import (
	"bytes"
	"flag"
	"fmt"
	"math"
	"math/rand"
	"os"
	"path/filepath"
	"runtime/debug"
	"sort"

	bolt "go.etcd.io/bbolt"
)

type bkt = map[string]string
type data = map[string]bkt

func clone(d data) data {
	o := data{}
	for n, m := range d {
		mm := bkt{}
		for k, v := range m {
			mm[k] = v
		}
		o[n] = mm
	}
	return o
}

func ents(m bkt) []string {
	ks := make([]string, 0, len(m))
	for k := range m {
		ks = append(ks, k)
	}
	sort.Strings(ks) // bytewise, as GoStringLt
	return ks
}

type kept struct {
	s    []byte
	want string
	what string
}

type rtx struct {
	tx   *bolt.Tx
	snap data
	kept []kept
}

type st struct {
	r      *rand.Rand
	db     *bolt.DB
	D      data
	w      *bolt.Tx
	S      data
	wkept  []kept
	hs     map[string]*bolt.Bucket // current handles
	old    []*bolt.Bucket          // handles of deleted buckets (FillPercent only)
	rs     []*rtx
	log    []string
	nops   int
	verbose bool
}

func (s *st) logf(f string, a ...any) {
	s.log = append(s.log, fmt.Sprintf(f, a...))
	if len(s.log) > 400 {
		s.log = s.log[len(s.log)-400:]
	}
}

type bad struct{ msg string }

func fail(f string, a ...any) { panic(bad{fmt.Sprintf(f, a...)}) }

var names = []string{"a", "b", "c", "\xff", "a\x00"}

func (s *st) key() string {
	r := s.r
	switch r.Intn(10) {
	case 0:
		return string([]byte{byte(r.Intn(256))})
	case 1:
		n := 1 + r.Intn(2000)
		b := make([]byte, n)
		r.Read(b)
		return string(b)
	case 2:
		if r.Intn(20) == 0 {
			n := 32768 - r.Intn(3)
			b := bytes.Repeat([]byte{byte('A' + r.Intn(3))}, n)
			return string(b)
		}
		fallthrough
	default:
		return fmt.Sprintf("k%05d", r.Intn(3000))
	}
}

func (s *st) value() []byte {
	r := s.r
	switch r.Intn(12) {
	case 0:
		return nil
	case 1:
		return []byte{}
	case 2:
		b := make([]byte, 3000+r.Intn(20000))
		r.Read(b)
		return b
	case 3:
		b := make([]byte, 4000+r.Intn(200))
		r.Read(b)
		return b
	default:
		b := make([]byte, r.Intn(300))
		r.Read(b)
		return b
	}
}

func (s *st) checkKept() {
	for i, k := range s.wkept {
		if string(k.s) != k.want {
			fail("write-tx slice %d (%s) changed: %q... want %q...", i, k.what, trunc(string(k.s)), trunc(k.want))
		}
	}
	for j, rt := range s.rs {
		for i, k := range rt.kept {
			if string(k.s) != k.want {
				fail("read-tx %d slice %d (%s) changed: %q... want %q...", j, i, k.what, trunc(string(k.s)), trunc(k.want))
			}
		}
	}
}

func trunc(x string) string {
	if len(x) > 24 {
		return fmt.Sprintf("%q(len %d)", x[:24], len(x))
	}
	return fmt.Sprintf("%q", x)
}

// scan: Seek a random key, then Next a few times, comparing with the model's entries.
func (s *st) scan(c *bolt.Cursor, m bkt, keep *[]kept, who string) {
	es := ents(m)
	sk := s.key()
	if s.r.Intn(4) == 0 && len(es) > 0 {
		sk = es[s.r.Intn(len(es))]
	}
	i := sort.SearchStrings(es, sk)
	k, v := c.Seek([]byte(sk))
	n := s.r.Intn(40)
	for step := 0; ; step++ {
		if i < len(es) {
			if k == nil || string(k) != es[i] || string(v) != m[es[i]] {
				fail("%s cursor at model index %d: got key %s val %s, want key %s val %s", who, i, trunc(string(k)), trunc(string(v)), trunc(es[i]), trunc(m[es[i]]))
			}
			if s.r.Intn(3) == 0 {
				*keep = append(*keep, kept{k, es[i], who + " key"}, kept{v, m[es[i]], who + " val"})
			}
		} else if k != nil || v != nil {
			fail("%s cursor past end (index %d of %d): got key %s", who, i, len(es), trunc(string(k)))
		}
		if step >= n {
			break
		}
		k, v = c.Next()
		if i < len(es) {
			i++
		}
	}
}

func (s *st) begin() {
	tx, err := s.db.Begin(true)
	if err != nil {
		fail("Begin(true): %v", err)
	}
	s.w, s.S, s.wkept, s.hs, s.old = tx, clone(s.D), nil, map[string]*bolt.Bucket{}, nil
}

var nosync = flag.Bool("nosync", true, "open with Options.NoSync (no fsync per commit; OptsM.ok allows it)")
var grow = flag.Bool("grow", true, "operation weights that grow big trees (false: step's uniform 0..99 scale)")
var plantModel = flag.Bool("plant-model", false, "drop one Put from the model (sanity check)")

// pickOp maps to the 0..99 scale of step's cases.
func (s *st) pickOp() int {
	if !*grow {
		return s.r.Intn(100)
	}
	x := s.r.Intn(1000)
	switch {
	case x < 600:
		return s.r.Intn(40) // Put
	case x < 700:
		return 40 + s.r.Intn(15) // Delete
	case x < 708:
		return 55 + s.r.Intn(5) // bulk delete
	case x < 730:
		return 60 + s.r.Intn(6) // Create
	case x < 733:
		return 66 + s.r.Intn(3) // DeleteBucket
	case x < 760:
		return 69 + s.r.Intn(3)
	case x < 790:
		return 72 + s.r.Intn(4) // FillPercent
	case x < 880:
		return 76 + s.r.Intn(8) // write scan
	case x < 905:
		return 84 + s.r.Intn(5) // Commit
	case x < 925:
		return 89 + s.r.Intn(4)
	case x < 990:
		return 93 + s.r.Intn(5)
	default:
		return 98 + s.r.Intn(2)
	}
}

func (s *st) step() {
	r := s.r
	s.nops++
	switch op := s.pickOp(); {
	case op < 40: // Put
		n := names[r.Intn(len(names))]
		b := s.hs[n]
		if b == nil || s.S[n] == nil {
			return
		}
		k, v := s.key(), s.value()
		s.logf("Put(%q, %s, len %d)", n, trunc(k), len(v))
		if err := b.Put([]byte(k), v); err != nil {
			fail("Put: %v", err)
		}
		if *plantModel && s.nops > 500 && s.nops%997 == 0 {
			return
		}
		s.S[n][k] = string(v)
	case op < 55: // Delete
		n := names[r.Intn(len(names))]
		b := s.hs[n]
		if b == nil || s.S[n] == nil {
			return
		}
		k := s.key()
		if es := ents(s.S[n]); len(es) > 0 && r.Intn(2) == 0 {
			k = es[r.Intn(len(es))]
		}
		s.logf("Delete(%q, %s)", n, trunc(k))
		if err := b.Delete([]byte(k)); err != nil {
			fail("Delete: %v", err)
		}
		delete(s.S[n], k)
	case op < 60: // bulk delete a range, to empty leaves
		n := names[r.Intn(len(names))]
		b := s.hs[n]
		if b == nil || s.S[n] == nil {
			return
		}
		es := ents(s.S[n])
		if len(es) == 0 {
			return
		}
		lo := r.Intn(len(es))
		hi := lo + r.Intn(len(es)-lo+1)
		s.logf("Delete range %q [%d,%d) of %d", n, lo, hi, len(es))
		for _, k := range es[lo:hi] {
			if err := b.Delete([]byte(k)); err != nil {
				fail("Delete: %v", err)
			}
			delete(s.S[n], k)
		}
	case op < 66: // CreateBucketIfNotExists
		n := names[r.Intn(len(names))]
		s.logf("CreateBucketIfNotExists(%q)", n)
		b, err := s.w.CreateBucketIfNotExists([]byte(n))
		if err != nil {
			fail("CreateBucketIfNotExists: %v", err)
		}
		if s.S[n] == nil {
			s.S[n] = bkt{}
		} else if s.hs[n] != nil && s.hs[n] != b {
			s.logf("(note: a second handle for %q)", n)
		}
		s.hs[n] = b
	case op < 69: // DeleteBucket
		n := names[r.Intn(len(names))]
		s.logf("DeleteBucket(%q)", n)
		err := s.w.DeleteBucket([]byte(n))
		if s.S[n] == nil {
			if err != bolt.ErrBucketNotFound {
				fail("DeleteBucket absent: %v", err)
			}
			return
		}
		if err != nil {
			fail("DeleteBucket: %v", err)
		}
		delete(s.S, n)
		if s.hs[n] != nil {
			s.old = append(s.old, s.hs[n])
		}
		delete(s.hs, n)
	case op < 72: // Tx.Bucket (write)
		n := names[r.Intn(len(names))]
		b := s.w.Bucket([]byte(n))
		if (b == nil) != (s.S[n] == nil) {
			fail("Tx.Bucket(%q) = %v, model present %v", n, b != nil, s.S[n] != nil)
		}
		if b != nil {
			s.hs[n] = b
		}
	case op < 76: // FillPercent: ownWTxG_fill, any bits
		hs := []*bolt.Bucket{}
		for _, b := range s.hs {
			hs = append(hs, b)
		}
		hs = append(hs, s.old...)
		if len(hs) == 0 {
			return
		}
		b := hs[r.Intn(len(hs))]
		var f float64
		switch r.Intn(8) {
		case 0:
			f = math.NaN()
		case 1:
			f = math.Inf(1)
		case 2:
			f = math.Inf(-1)
		case 3:
			f = 0
		case 4:
			f = -r.Float64() * 1e9
		case 5:
			f = math.Float64frombits(r.Uint64())
		default:
			f = r.Float64() * 2
		}
		s.logf("FillPercent = %v", f)
		b.FillPercent = f
	case op < 84: // write cursor scan (Cursor_kvw; returned before the next Put)
		n := names[r.Intn(len(names))]
		b := s.hs[n]
		if b == nil || s.S[n] == nil {
			return
		}
		s.logf("write scan %q", n)
		s.scan(b.Cursor(), s.S[n], &s.wkept, "write")
	case op < 89: // Commit, then Begin
		s.logf("Commit (readers open: %d)", len(s.rs))
		if err := s.w.Commit(); err != nil {
			fail("Commit: %v", err)
		}
		s.D = s.S
		s.wkept = nil
		s.begin()
	case op < 93: // Begin a reader
		if len(s.rs) >= 4 {
			return
		}
		tx, err := s.db.Begin(false)
		if err != nil {
			fail("Begin(false): %v", err)
		}
		s.logf("Begin read #%d", len(s.rs))
		s.rs = append(s.rs, &rtx{tx: tx, snap: clone(s.D)})
	case op < 98: // reader scan
		if len(s.rs) == 0 {
			return
		}
		rt := s.rs[r.Intn(len(s.rs))]
		n := names[r.Intn(len(names))]
		b := rt.tx.Bucket([]byte(n))
		if (b == nil) != (rt.snap[n] == nil) {
			fail("read Tx.Bucket(%q) = %v, snapshot present %v", n, b != nil, rt.snap[n] != nil)
		}
		if b != nil {
			s.logf("read scan %q", n)
			s.scan(b.Cursor(), rt.snap[n], &rt.kept, "read")
		}
	default: // Rollback a reader
		if len(s.rs) == 0 {
			return
		}
		i := r.Intn(len(s.rs))
		s.logf("Rollback read #%d", i)
		if err := s.rs[i].tx.Rollback(); err != nil {
			fail("Rollback: %v", err)
		}
		s.rs = append(s.rs[:i], s.rs[i+1:]...)
	}
}

func run(seed int64, n int, dir string) (msg string, log []string) {
	s := &st{r: rand.New(rand.NewSource(seed))}
	p := filepath.Join(dir, fmt.Sprintf("db%d", seed))
	defer os.Remove(p)
	db, err := bolt.Open(p, 0600, &bolt.Options{InitialMmapSize: 1 << 30, NoSync: *nosync})
	if err != nil {
		return "Open: " + err.Error(), nil
	}
	s.db, s.D = db, data{}
	defer func() {
		x := recover()
		if x != nil {
			if b, ok := x.(bad); ok {
				msg = b.msg
			} else {
				msg = fmt.Sprintf("PANIC: %v\n%s", x, debug.Stack())
			}
			log = s.log
		}
		// cleanup without hanging on a broken db
		go func() {
			for _, rt := range s.rs {
				rt.tx.Rollback()
			}
			if s.w != nil {
				s.w.Rollback()
			}
			db.Close()
		}()
	}()
	s.begin()
	for i := 0; i < n; i++ {
		s.step()
		s.checkKept()
	}
	if *showStats {
		for _, nm := range names {
			if b := s.w.Bucket([]byte(nm)); b != nil {
				st := b.Stats()
				fmt.Printf("  seed %d bucket %q: keys %d depth %d branch pages %d leaf pages %d overflow %d\n", seed, nm, st.KeyN, st.Depth, st.BranchPageN, st.LeafPageN, st.LeafOverflowN)
			}
		}
	}
	return "", nil
}

var showStats = flag.Bool("stats", false, "print each bucket's shape at the end of a run")

func main() {
	runs := flag.Int("runs", 200, "number of runs")
	steps := flag.Int("steps", 3000, "operations per run")
	seed := flag.Int64("seed", 1, "first seed (run i uses seed+i)")
	dir := flag.String("dir", os.TempDir(), "directory for the database files")
	flag.Parse()
	found := 0
	for i := 0; i < *runs; i++ {
		sd := *seed + int64(i)
		msg, log := run(sd, *steps, *dir)
		if msg != "" {
			found++
			fmt.Printf("seed %d: %s\n", sd, msg)
			for _, l := range log[max(0, len(log)-15):] {
				fmt.Println("   ", l)
			}
			if found >= 5 {
				break
			}
		}
	}
	fmt.Printf("runs %d, found %d\n", *runs, found)
	if found > 0 {
		os.Exit(1)
	}
}
