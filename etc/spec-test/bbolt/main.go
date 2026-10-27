// Command bbolt-spec-test tests bbolt's trust-boundary specs (Spec/go_etcd_io/bbolt/*.lean, over
// the predicates of Proof/go_etcd_io/etcd/server/v3/storage/backend/InvBbolt.lean) against the
// real bbolt (v1.5.0, the version etcd's backend uses): step 2 of notes/spec-first-plan.md.
//
// The specs are the generator and the oracle. The tester keeps the spec-level state of a run --
// the instances of the abstract predicates the specs have given out (ownDB, wrTok, isDB, txLive,
// ownWTx, wBkt, ownCur, ...) with their pure arguments (the data D, S, a cursor's entries) -- and
// at each step makes one call whose precondition that state satisfies: it consumes the
// precondition's exclusive predicates (persistent ones stay), runs the call on the real bbolt, and
// checks the postcondition's pure part against what the call returned. A panic, or a result the
// postcondition excludes, refutes the spec: the call's precondition held in a state the specs
// themselves reached. Then the postcondition's predicates are added, with the pure arguments the
// postcondition gives them.
//
// What it checks is therefore not only each spec's pure part: a persistent predicate that should
// not outlive an operation (isDB after Close, wBkt after DeleteBucket), or a resource given back
// too early (a write cursor's ownWTx), lets the tester make a call the specs allow and Go does not
// survive, or that returns what the model says it cannot.
//
// Each spec is transcribed by hand from its Lean statement (the comment on each step cites it).
// The -old flags select the statements the axiom audit found false (notes/audit.md, "bbolt"), as
// they were before audit B4b (commit 39dd386a43).
package main

import (
	"bytes"
	"errors"
	"flag"
	"fmt"
	"math/rand"
	"os"
	"path/filepath"
	"sort"
	"strings"
	"time"

	bolt "go.etcd.io/bbolt"
	berrors "go.etcd.io/bbolt/errors"
)

// ---- the pure model: InvBbolt.lean's Data, BktData, bktEnts, seekIdx, maxKeySize ----

type BktData map[string]string
type Data map[string]BktData

type Ent struct{ k, v string }

func (m BktData) clone() BktData {
	r := BktData{}
	for k, v := range m {
		r[k] = v
	}
	return r
}

func (d Data) clone() Data {
	r := Data{}
	for n, m := range d {
		r[n] = m.clone()
	}
	return r
}

// bktEnts m: the entries sorted by key (bytewise, strLt).
func bktEnts(m BktData) []Ent {
	es := make([]Ent, 0, len(m))
	for k, v := range m {
		es = append(es, Ent{k, v})
	}
	sort.Slice(es, func(i, j int) bool { return es[i].k < es[j].k })
	return es
}

// seekIdx es k: the first index whose key is not below k.
func seekIdx(es []Ent, k string) int {
	i := 0
	for i < len(es) && (es[i].k < k || *mutant == "seek-gt" && es[i].k == k) {
		i++
	}
	return i
}

const maxKeySize = 32768

// ---- the spec-level state: the predicate instances a run holds ----

type dbG struct {
	h      *bolt.DB
	path   string
	isDB   bool // persistent
	ownDB  bool // ownDB db γ D (γ: one per db)
	D      Data
	wrTok  bool
	closed bool // Go-level fact, used only to avoid calls that block (partial correctness)
}

func (d *dbG) name() string { return filepath.Base(d.path) }

type txG struct {
	h        *bolt.Tx
	db       *dbG
	write    bool
	txDB     bool // persistent
	txLive   bool // txLive tx 1 (for a writer: only while lent out of ownWTx, see below)
	rtxSnap  *Data
	rtxStats bool
	ownWTx   bool // ownWTx tx γ D S
	D, S     Data
	txDone   bool // persistent
	// The current Cursor_kvw: a cursor holding txLive tx 1 and the wand back to ownWTx.
	wandCur *curG
}

type curG struct {
	h     *bolt.Cursor
	tx    *txG
	owned bool // ownCur tx c es pos
	es    []Ent
	pos   int // -1: none
}

type bktW struct { // wBkt tx b n, persistent
	tx *txG
	h  *bolt.Bucket
	n  string
	id int // the handle's number in the run's log
}

type bktR struct { // rBkt tx b es, persistent
	tx *txG
	h  *bolt.Bucket
	es []Ent
}

type state struct {
	dbs   []*dbG
	txs   []*txG
	curs  []*curG
	wbkts []bktW
	rbkts []bktR
	dir   string
	nfile int
	nbkt  int
	log   []string
}

// Spec variants.
var (
	oldInfo      = flag.Bool("old-info", false, "DB.Info_kv as before audit B4b: precondition isDB db only")
	oldCursorKvw = flag.Bool("old-cursor-kvw", false, "Bucket.Cursor_kvw as before audit B4b: ownWTx given back at once")
	runs         = flag.Int("runs", 2000, "number of runs")
	steps        = flag.Int("steps", 60, "calls per run")
	seed         = flag.Int64("seed", 1, "first seed")
	verbose      = flag.Bool("v", false, "print every run's trace")
	fixWBkt      = flag.Bool("fix-wbkt", false, "wBkt tx b n not persistent across DeleteBucket n (a corrected statement; the current one is false)")
	mutant       = flag.String("mutant", "", "a deliberately wrong spec: seek-gt, wrtok-dup, commit-old, rollback-keeps-live, read-latest, create-resets, delete-noop")
	blockAfter   = flag.Duration("block-after", 100*time.Millisecond, "a call not returned by then is blocked")
)

type violation struct{ msg string }

// fail reports a refutation: the precondition held and the call did what the spec excludes.
func fail(format string, a ...any) { panic(violation{fmt.Sprintf(format, a...)}) }

// blocked ends a run whose call did not return: partial correctness allows blocking (a writer's
// remap waits for the readers, Close for every transaction), so it refutes nothing.
type blocked struct{ name string }

// call runs f, turning a Go panic into a refutation (a WP excludes panics); a call that has not
// returned after a while is taken as blocked.
func call(name string, f func()) {
	done := make(chan any, 1)
	go func() {
		defer func() { done <- recover() }()
		f()
	}()
	select {
	case r := <-done:
		if r != nil {
			fail("%s panicked: %v", name, r)
		}
	case <-time.After(*blockAfter):
		panic(blocked{name})
	}
}

var names = []string{"a", "b"}
var keys = []string{"k1", "k2", "k3"}

func (s *state) newW(t *txG, b *bolt.Bucket, n string) {
	s.nbkt++
	s.wbkts = append(s.wbkts, bktW{t, b, n, s.nbkt})
}

func (s *state) logf(format string, a ...any) { s.log = append(s.log, fmt.Sprintf(format, a...)) }

// txLiveFor: txLive tx 1 is available: a reader's own, or a writer's from ownWTx (ownWTx_live),
// or the one a write cursor holds.
func txLiveFor(t *txG) bool { return t.txLive || t.ownWTx }

// ---- the steps: one per axiom, each enabled when its precondition holds ----

type step struct {
	name string
	try  func(s *state, r *rand.Rand) bool // false: not enabled
}

func pick[T any](r *rand.Rand, xs []T) (T, bool) {
	var z T
	if len(xs) == 0 {
		return z, false
	}
	return xs[r.Intn(len(xs))], true
}

var stepsTable = []step{
	// Open_kv: fileHolds path D ∗ optsAt opts o ∗ ⌜o.ok⌝ (a fresh file: D = ∅; default options)
	// {err ≠ nil ∨ err = nil ∗ ∃ γ, ownDB db γ D ∗ wrTok γ ∗ isDB db}
	{"Open", func(s *state, r *rand.Rand) bool {
		if len(s.dbs) >= 2 {
			return false
		}
		s.nfile++
		p := filepath.Join(s.dir, fmt.Sprintf("db%d", s.nfile))
		var h *bolt.DB
		var err error
		call("Open", func() { h, err = bolt.Open(p, 0600, nil) })
		s.logf("Open(%s) = err %v", filepath.Base(p), err)
		if err == nil {
			s.dbs = append(s.dbs, &dbG{h: h, path: p, isDB: true, ownDB: true, D: Data{}, wrTok: true})
		}
		return true
	}},
	// DB.Begin_kv: ownDB db γ D ∗ (w → wrTok γ)
	// {ownDB db γ D ∗ isDB db ∗ (err ≠ nil ∗ (w → wrTok) ∨ err = nil ∗ txDB tx db ∗
	//   (w → ownWTx tx γ D D) ∧ (¬w → txLive tx 1 ∗ rtxSnap tx D ∗ rtxStats tx))}
	{"Begin", func(s *state, r *rand.Rand) bool {
		d, ok := pick(r, s.dbs)
		if !ok || !d.ownDB {
			return false
		}
		w := r.Intn(2) == 0
		if w && !d.wrTok {
			return false
		}
		var h *bolt.Tx
		var err error
		call("Begin", func() { h, err = d.h.Begin(w) })
		s.logf("Begin(%s, %v) = err %v", d.name(), w, err)
		if err != nil {
			return true
		}
		t := &txG{h: h, db: d, write: w, txDB: true}
		if w {
			d.wrTok = *mutant == "wrtok-dup"
			t.ownWTx, t.D, t.S = true, d.D, d.D.clone()
		} else {
			snap := d.D
			t.txLive, t.rtxSnap, t.rtxStats = true, &snap, true
		}
		s.txs = append(s.txs, t)
		return true
	}},
	// Tx.Commit_kv: ownDB db γ D ∗ txDB tx db ∗ ownWTx tx γ D S
	// {txDone tx ∗ (err = nil ∗ ownDB db γ S ∗ wrTok γ ∨ err ≠ nil)}
	{"Commit", func(s *state, r *rand.Rand) bool {
		t, ok := pick(r, s.txs)
		if !ok || !t.ownWTx || !t.txDB || !t.db.ownDB {
			return false
		}
		var err error
		call("Commit", func() { err = t.h.Commit() })
		s.logf("Commit(tx) = err %v", err)
		t.ownWTx, t.txDone = false, true
		t.db.ownDB = false
		if err == nil {
			t.db.ownDB, t.db.D, t.db.wrTok = true, t.S, true
			if *mutant == "commit-old" {
				t.db.D = t.D
			}
		}
		return true
	}},
	// Tx.Rollback_kv: txLive tx 1 ∗ rtxSnap tx D  {RET nil; txDone tx}
	{"Rollback", func(s *state, r *rand.Rand) bool {
		t, ok := pick(r, s.txs)
		if !ok || !t.txLive || t.rtxSnap == nil || t.wandCur != nil {
			return false
		}
		var err error
		call("Rollback", func() { err = t.h.Rollback() })
		s.logf("Rollback(rtx) = err %v", err)
		if err != nil {
			fail("Rollback returned %v, spec says nil", err)
		}
		t.txLive, t.txDone = *mutant == "rollback-keeps-live", true
		return true
	}},
	// Tx.Bucket_kvr: txLive tx q ∗ rtxSnap tx D ∗ rtxStats tx
	// {(D n = none ∧ b = null) ∨ ∃ m, D n = some m ∧ b ≠ null ∗ rBkt tx b (bktEnts m)}
	{"Tx.Bucket(r)", func(s *state, r *rand.Rand) bool {
		t, ok := pick(r, s.txs)
		if !ok || !t.txLive || t.rtxSnap == nil || !t.rtxStats {
			return false
		}
		n := names[r.Intn(len(names))]
		var b *bolt.Bucket
		call("Tx.Bucket", func() { b = t.h.Bucket([]byte(n)) })
		s.logf("Tx.Bucket(rtx, %s) = %v", n, b != nil)
		snap := *t.rtxSnap
		if *mutant == "read-latest" {
			snap = t.db.D
		}
		m, found := snap[n]
		if found != (b != nil) {
			fail("read Tx.Bucket(%s): bucket in snapshot %v, Go handle non-nil %v", n, found, b != nil)
		}
		if b != nil {
			s.rbkts = append(s.rbkts, bktR{t, b, bktEnts(m)})
		}
		return true
	}},
	// Tx.Bucket_kvw: ownWTx tx γ D S
	// {ownWTx tx γ D S ∗ (S n = none ∧ b = null ∨ S n ≠ none ∧ b ≠ null ∗ wBkt tx b n)}
	{"Tx.Bucket(w)", func(s *state, r *rand.Rand) bool {
		t, ok := pick(r, s.txs)
		if !ok || !t.ownWTx {
			return false
		}
		n := names[r.Intn(len(names))]
		var b *bolt.Bucket
		call("Tx.Bucket", func() { b = t.h.Bucket([]byte(n)) })
		s.logf("Tx.Bucket(wtx, %s) = %v (handle #%d)", n, b != nil, s.nbkt+1)
		_, found := t.S[n]
		if found != (b != nil) {
			fail("write Tx.Bucket(%s): bucket in S %v, Go handle non-nil %v", n, found, b != nil)
		}
		if b != nil {
			s.newW(t, b, n)
		}
		return true
	}},
	// Tx.CreateBucketIfNotExists_kv: 0 < |n| ≤ maxKeySize → ownWTx tx γ D S
	// {err = nil ∗ ownWTx tx γ D (S n = none ? S[n := ∅] : S) ∗ wBkt tx b n}
	{"CreateBucketIfNotExists", func(s *state, r *rand.Rand) bool {
		t, ok := pick(r, s.txs)
		if !ok || !t.ownWTx {
			return false
		}
		n := names[r.Intn(len(names))]
		var b *bolt.Bucket
		var err error
		call("CreateBucketIfNotExists", func() { b, err = t.h.CreateBucketIfNotExists([]byte(n)) })
		s.logf("CreateBucketIfNotExists(%s) = err %v (handle #%d)", n, err, s.nbkt+1)
		if err != nil {
			fail("CreateBucketIfNotExists(%s) returned %v, spec says nil", n, err)
		}
		if _, found := t.S[n]; !found || *mutant == "create-resets" {
			t.S[n] = BktData{}
		}
		s.newW(t, b, n)
		return true
	}},
	// Tx.DeleteBucket_kv: ownWTx tx γ D S
	// {(S n = none ∗ ownWTx tx γ D S ∗ err = ErrBucketNotFound) ∨
	//  (S n ≠ none ∧ err = nil ∗ ownWTx tx γ D (S.delete n))}
	{"DeleteBucket", func(s *state, r *rand.Rand) bool {
		t, ok := pick(r, s.txs)
		if !ok || !t.ownWTx {
			return false
		}
		n := names[r.Intn(len(names))]
		var err error
		call("DeleteBucket", func() { err = t.h.DeleteBucket([]byte(n)) })
		s.logf("DeleteBucket(%s) = err %v", n, err)
		if _, found := t.S[n]; found {
			if err != nil {
				fail("DeleteBucket(%s) of an existing bucket returned %v", n, err)
			}
			delete(t.S, n)
			if *fixWBkt {
				// A corrected wBkt: the handles of the deleted bucket are no longer the bucket's.
				var keep []bktW
				for _, w := range s.wbkts {
					if w.tx != t || w.n != n {
						keep = append(keep, w)
					}
				}
				s.wbkts = keep
			}
		} else if !errors.Is(err, berrors.ErrBucketNotFound) {
			fail("DeleteBucket(%s) of a missing bucket returned %v, spec says ErrBucketNotFound", n, err)
		}
		return true
	}},
	// Bucket.Put_kv: S n = some m → 0 < |k| ≤ maxKeySize → ownWTx tx γ D S ∗ wBkt tx b n
	// {|v| ≤ maxValueSize ∧ err = nil ∗ ownWTx tx γ D S[n := m[k := v]] ∨ ...}
	{"Put", func(s *state, r *rand.Rand) bool {
		w, ok := pick(r, s.wbkts)
		if !ok || !w.tx.ownWTx {
			return false
		}
		m, found := w.tx.S[w.n]
		if !found {
			return false
		}
		k, v := keys[r.Intn(len(keys))], fmt.Sprintf("v%d", r.Intn(100))
		var err error
		s.logf("Put(#%d %s: %s=%s) ...", w.id, w.n, k, v)
		call("Put", func() { err = w.h.Put([]byte(k), []byte(v)) })
		s.logf("  = err %v", err)
		if err != nil {
			fail("Put returned %v, spec says nil", err)
		}
		m = m.clone()
		m[k] = v
		w.tx.S[w.n] = m
		return true
	}},
	// Bucket.Delete_kv: S n = some m → ownWTx tx γ D S ∗ wBkt tx b n
	// {RET nil; ownWTx tx γ D S[n := m.delete k]}
	{"Delete", func(s *state, r *rand.Rand) bool {
		w, ok := pick(r, s.wbkts)
		if !ok || !w.tx.ownWTx {
			return false
		}
		m, found := w.tx.S[w.n]
		if !found {
			return false
		}
		k := keys[r.Intn(len(keys))]
		var err error
		s.logf("Delete(#%d %s: %s) ...", w.id, w.n, k)
		call("Delete", func() { err = w.h.Delete([]byte(k)) })
		s.logf("  = err %v", err)
		if err != nil {
			fail("Delete returned %v, spec says nil", err)
		}
		m = m.clone()
		if *mutant != "delete-noop" {
			delete(m, k)
		}
		w.tx.S[w.n] = m
		return true
	}},
	// Bucket.Cursor_kvr: rBkt tx b es ∗ rtxStats tx ∗ txLive tx q  {ownCur tx c es none ∗ ...}
	{"Cursor(r)", func(s *state, r *rand.Rand) bool {
		b, ok := pick(r, s.rbkts)
		if !ok || !b.tx.txLive || !b.tx.rtxStats {
			return false
		}
		var c *bolt.Cursor
		call("Cursor", func() { c = b.h.Cursor() })
		s.logf("Cursor(rbkt) ")
		s.curs = append(s.curs, &curG{h: c, tx: b.tx, owned: true, es: b.es, pos: -1})
		return true
	}},
	// Bucket.Cursor_kvw: S n = some m → ownWTx tx γ D S ∗ wBkt tx b n
	// current: {ownCur tx c (bktEnts m) none ∗ txLive tx 1 ∗
	//           (∀ pos, ownCur tx c (bktEnts m) pos -∗ txLive tx 1 -∗ ownWTx tx γ D S)}
	// old:     {ownCur tx c (bktEnts m) none ∗ ownWTx tx γ D S}
	{"Cursor(w)", func(s *state, r *rand.Rand) bool {
		w, ok := pick(r, s.wbkts)
		if !ok || !w.tx.ownWTx {
			return false
		}
		m, found := w.tx.S[w.n]
		if !found {
			return false
		}
		var c *bolt.Cursor
		call("Cursor", func() { c = w.h.Cursor() })
		s.logf("Cursor(#%d %s)", w.id, w.n)
		cg := &curG{h: c, tx: w.tx, owned: true, es: bktEnts(m), pos: -1}
		s.curs = append(s.curs, cg)
		if !*oldCursorKvw {
			w.tx.ownWTx, w.tx.txLive, w.tx.wandCur = false, true, cg
		}
		return true
	}},
	// The wand of Cursor_kvw (a ghost step, no Go call): ownCur tx c es pos ∗ txLive tx 1 -∗ ownWTx.
	{"(close write cursor)", func(s *state, r *rand.Rand) bool {
		t, ok := pick(r, s.txs)
		if !ok || t.wandCur == nil || !t.wandCur.owned || !t.txLive {
			return false
		}
		t.wandCur.owned, t.txLive, t.ownWTx, t.wandCur = false, false, true, nil
		s.logf("(write cursor given back)")
		return true
	}},
	// Cursor.Seek_kv: ownCur tx c es pos ∗ txLive tx q
	// {ownCur tx c es (some (seekIdx es k)) ∗ curAt tx es (seekIdx es k) k' v'}
	{"Seek", func(s *state, r *rand.Rand) bool {
		c, ok := pick(r, s.curs)
		if !ok || !c.owned || !txLiveFor(c.tx) {
			return false
		}
		key := keys[r.Intn(len(keys))]
		if r.Intn(4) == 0 {
			key = "k0"
		}
		var k, v []byte
		call("Seek", func() { k, v = c.h.Seek([]byte(key)) })
		i := seekIdx(c.es, key)
		s.logf("Seek(%s) = %q,%q (model: index %d of %v)", key, k, v, i, c.es)
		checkCurAt(c, i, k, v)
		c.pos = i
		return true
	}},
	// Cursor.Next_kv: ownCur tx c es (some i) ∗ txLive tx q
	// {ownCur tx c es (some (min (i+1) |es|)) ∗ curAt tx es (i+1) k v}
	{"Next", func(s *state, r *rand.Rand) bool {
		c, ok := pick(r, s.curs)
		if !ok || !c.owned || c.pos < 0 || !txLiveFor(c.tx) {
			return false
		}
		var k, v []byte
		call("Next", func() { k, v = c.h.Next() })
		s.logf("Next() = %q,%q (model: index %d of %v)", k, v, c.pos+1, c.es)
		checkCurAt(c, c.pos+1, k, v)
		c.pos = min(c.pos+1, len(c.es))
		return true
	}},
	// DB.Info_kv: current: isDB db ∗ txDB tx db ∗ txLive tx q; old: isDB db.
	// {(i : Loc), RET i; ∃ v, i ↦□ v}
	{"Info", func(s *state, r *rand.Rand) bool {
		d, ok := pick(r, s.dbs)
		if !ok || !d.isDB {
			return false
		}
		if !*oldInfo {
			live := false
			for _, t := range s.txs {
				if t.db == d && t.txDB && txLiveFor(t) {
					live = true
				}
			}
			if !live {
				return false
			}
		}
		var i *bolt.Info
		call("Info", func() { i = d.h.Info() })
		s.logf("Info(%s) = %v", d.name(), i != nil)
		if i == nil {
			fail("Info returned nil, spec says a points-to")
		}
		return true
	}},
	// DB.Stats_kv: isDB db  {True}
	{"Stats", func(s *state, r *rand.Rand) bool {
		d, ok := pick(r, s.dbs)
		if !ok || !d.isDB {
			return false
		}
		call("Stats", func() { _ = d.h.Stats() })
		s.logf("Stats(%s)", d.name())
		return true
	}},
	// DB.Close_kv: isDB db  {err = nil ∨ ¬ dbCloseOk}  (dbCloseOk holds here: a local file)
	{"Close", func(s *state, r *rand.Rand) bool {
		d, ok := pick(r, s.dbs)
		if !ok || !d.isDB {
			return false
		}
		// Close waits for every open transaction (partial correctness allows blocking); the
		// tester runs one thread, so it does not make a call that would block forever.
		for _, t := range s.txs {
			if t.db == d && !t.txDone && t.h.DB() != nil {
				return false
			}
		}
		var err error
		call("Close", func() { err = d.h.Close() })
		s.logf("Close(%s) = err %v", d.name(), err)
		if err != nil {
			fail("Close returned %v", err)
		}
		d.closed = true
		return true
	}},
	// Tx.Size_kv: txLive tx q  {RET n; txLive tx q}
	{"Tx.Size", func(s *state, r *rand.Rand) bool {
		t, ok := pick(r, s.txs)
		if !ok || !txLiveFor(t) {
			return false
		}
		call("Tx.Size", func() { _ = t.h.Size() })
		s.logf("Tx.Size")
		return true
	}},
	// Tx.Stats_kv: txDone tx  {True}
	{"Tx.Stats", func(s *state, r *rand.Rand) bool {
		t, ok := pick(r, s.txs)
		if !ok || !t.txDone {
			return false
		}
		call("Tx.Stats", func() { _ = t.h.Stats() })
		s.logf("Tx.Stats")
		return true
	}},
	// Tx.DB_kv: txLive tx q ∗ txDB tx db  {RET db}
	{"Tx.DB", func(s *state, r *rand.Rand) bool {
		t, ok := pick(r, s.txs)
		if !ok || !txLiveFor(t) || !t.txDB {
			return false
		}
		var h *bolt.DB
		call("Tx.DB", func() { h = t.h.DB() })
		s.logf("Tx.DB")
		if h != t.db.h {
			fail("Tx.DB returned %p, spec says the transaction's db %p", h, t.db.h)
		}
		return true
	}},
}

// checkCurAt: curAt tx es i k v -- es[i] = (k, v) with k non-nil, or k = v = nil past the end.
func checkCurAt(c *curG, i int, k, v []byte) {
	if i < len(c.es) {
		e := c.es[i]
		if k == nil || !bytes.Equal(k, []byte(e.k)) || !bytes.Equal(v, []byte(e.v)) {
			fail("cursor at index %d: Go returned %q=%q, spec says %q=%q (entries %v)", i, k, v, e.k, e.v, c.es)
		}
	} else if k != nil || v != nil {
		fail("cursor past the end (index %d of %d): Go returned %q=%q, spec says nil, nil", i, len(c.es), k, v)
	}
}

// run makes one run of up to n calls; it returns the refutation, if any.
func run(sd int64, n int) (msg string, log []string) {
	r := rand.New(rand.NewSource(sd))
	dir, err := os.MkdirTemp("", "bbolt-spec")
	if err != nil {
		panic(err)
	}
	s := &state{dir: dir}
	defer func() {
		x := recover()
		if b, ok := x.(blocked); ok {
			// The blocked call's goroutine holds bbolt's locks: leave the run's databases open.
			msg, log = "", append(s.log, "BLOCKED: "+b.name)
			blockedRuns++
			return
		}
		for _, t := range s.txs {
			if !t.txDone && t.h.DB() != nil {
				_ = t.h.Rollback()
			}
		}
		for _, d := range s.dbs {
			_ = d.h.Close()
		}
		os.RemoveAll(dir)
		if x != nil {
			v, ok := x.(violation)
			if !ok {
				panic(x)
			}
			msg, log = v.msg, s.log
		}
	}()
	stepsTable[0].try(s, r) // Open
	for done := 0; done < n; {
		st := stepsTable[r.Intn(len(stepsTable))]
		if st.try(s, r) {
			coverage[st.name]++
			done++
		}
	}
	return "", s.log
}

var blockedRuns int
var coverage = map[string]int{}

func main() {
	flag.Parse()
	refuted := map[string]int{}
	total := 0
	first := map[string]int64{}
	example := map[string][]string{}
	for i := 0; i < *runs; i++ {
		sd := *seed + int64(i)
		msg, log := run(sd, *steps)
		if *verbose {
			fmt.Printf("run %d:\n  %s\n", sd, strings.Join(log, "\n  "))
		}
		if msg == "" {
			continue
		}
		// Group refutations by the failing call (the message up to its first colon or space).
		key := msg
		if j := strings.IndexAny(msg, ":(,"); j > 0 {
			key = msg[:j]
		}
		total++
		if refuted[key] == 0 {
			first[key], example[key] = sd, append(log, "REFUTED: "+msg)
		}
		refuted[key]++
	}
	fmt.Printf("runs %d, steps %d, old-info %v, old-cursor-kvw %v, fix-wbkt %v; %d refuted, %d ended blocked\n",
		*runs, *steps, *oldInfo, *oldCursorKvw, *fixWBkt, total, blockedRuns)
	if *mutant != "" {
		fmt.Printf("mutant %s\n", *mutant)
	}
	var cov []string
	for _, st := range stepsTable {
		cov = append(cov, fmt.Sprintf("%s %d", st.name, coverage[st.name]))
	}
	fmt.Printf("calls made: %s\n", strings.Join(cov, ", "))
	if len(refuted) == 0 {
		fmt.Println("no refutation")
		return
	}
	for k, c := range refuted {
		fmt.Printf("\n%s: refuted in %d runs; first, seed %d:\n  %s\n", k, c, first[k], strings.Join(example[k], "\n  "))
	}
	os.Exit(1)
}
