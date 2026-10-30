// Package mvccrand is a randomized differential tester of etcd's mvcc key-value store in
// isolation: one store (mvcc.NewStore) over a backend in a fresh file and no lessor
// (lease.FakeLessor, as mvcc's own tests), driven by a seeded pseudo-random sequence of
// operations, each result checked against a reference model that keeps the state at every
// revision. Run panics if a check fails.
//
// The operations, through mvcc's public API (mvcc.KV):
//   - write transactions (Write ... End) of one to three puts and range deletes, with range reads
//     inside the transaction (which see its pending changes); the store's own Put and DeleteRange
//     (a transaction each);
//   - read transactions (Read ... End) and the store's own Range, at the current revision, a past
//     one, a future one (ErrFutureRev) or one below the compaction revision (ErrCompacted), over a
//     single key, a range or a from-key range, with a limit, count-only, keys-only and the total
//     count, every field of every key-value checked (key, value, create and mod revisions,
//     version, lease);
//   - compactions (Compact, then a wait for the job), at a revision above the compaction revision
//     (the current one half the time), at or below it (ErrCompacted) or above the current one
//     (ErrFutureRev). A compacted revision may be one whose transaction deleted a key and put it
//     again (issues/etcd-compaction-delete-then-put.md: fixed at the etcd pin, e7bb9f2de).
//
// Main is the test whose adequacy would be proved: it panics if a check fails.
package mvccrand

import (
	"context"

	"go.uber.org/zap"

	"go.etcd.io/etcd/api/v3/mvccpb"
	"go.etcd.io/etcd/pkg/v3/traceutil"
	"go.etcd.io/etcd/server/v3/lease"
	"go.etcd.io/etcd/server/v3/storage/backend"
	"go.etcd.io/etcd/server/v3/storage/mvcc"
)

// The keys, in increasing order (two of them extend another: a range's bounds are byte-wise).
var keys = []string{"a", "aa", "b", "ba", "c", "d"}

// The range ends besides the keys: past "ba" and below "c", and past every key.
var extraEnds = []string{"bb", "z"}

// A Config is a run's: the backend's file (fresh), the seed and the number of operations.
type Config struct {
	Path string
	Seed uint64
	Ops  int
}

// A rec is a key's key-value in the model.
type rec struct {
	val    string
	create int64
	mod    int64
	ver    int64
}

// A model is the store's expected history: states[r] is the state at revision r (the store
// starts at revision 1, empty; states[0] is the empty state too, never read), and the compaction
// revision.
type model struct {
	states    []map[string]rec
	compacted int64
}

func newModel() *model {
	return &model{states: []map[string]rec{{}, {}}, compacted: -1}
}

// cur is the store's current revision.
func (m *model) cur() int64 { return int64(len(m.states) - 1) }

// A rng is a splitmix64 generator.
type rng struct{ s uint64 }

func (r *rng) next() uint64 {
	r.s += 0x9e3779b97f4a7c15
	z := r.s
	z = (z ^ (z >> 30)) * 0xbf58476d1ce4e5b9
	z = (z ^ (z >> 27)) * 0x94d049bb133111eb
	return z ^ (z >> 31)
}

// intn returns a number in [0, n), n > 0.
func (r *rng) intn(n int) int { return int(r.next() % uint64(n)) }

func check(ok bool, msg string) {
	if !ok {
		panic("mvccrand: " + msg)
	}
}

func copyState(st map[string]rec) map[string]rec {
	c := make(map[string]rec, len(st))
	for k, v := range st {
		c[k] = v
	}
	return c
}

// A rangeReq is a range read's request: [key, end), end nil for the key alone, empty for every
// key from key on.
type rangeReq struct {
	key []byte
	end []byte
	ro  mvcc.RangeOptions
}

// inRange says whether key k is in the request's range.
func (q rangeReq) inRange(k string) bool {
	if q.end == nil {
		return k == string(q.key)
	}
	if k < string(q.key) {
		return false
	}
	return len(q.end) == 0 || k < string(q.end)
}

func (r *rng) genKey() []byte { return []byte(keys[r.intn(len(keys))]) }

// genEnd returns a range end: nil (one key) half the time, else empty (from key) or a key or an
// extra end.
func (r *rng) genEnd() []byte {
	switch r.intn(6) {
	case 0, 1, 2:
		return nil
	case 3:
		return []byte{}
	case 4:
		return []byte(extraEnds[r.intn(len(extraEnds))])
	default:
		return r.genKey()
	}
}

// genRange returns a range read's request at a revision up to past revisions past the current
// one cur: the current one (0), a revision from 0 to cur + 1 (cur + 1 is a future one), or a
// negative one (the current one too).
func (r *rng) genRange(cur int64) rangeReq {
	q := rangeReq{key: r.genKey(), end: r.genEnd()}
	switch r.intn(4) {
	case 0:
		q.ro.Rev = 0
	case 1:
		q.ro.Rev = -1
	default:
		q.ro.Rev = int64(r.intn(int(cur) + 2))
	}
	q.ro.Limit = int64(r.intn(4))
	q.ro.CountOnly = r.intn(5) == 0
	q.ro.FastKeysOnly = r.intn(4) == 0
	q.ro.WithTotalCount = r.intn(2) == 0
	return q
}

// checkRange checks a range read's result (res, err) against the states (states[r] at revision
// r), read at the revision cur (the read's), with the compaction revision compacted.
func checkRange(states []map[string]rec, cur int64, compacted int64, q rangeReq, res *mvcc.RangeResult, err error) {
	if q.ro.Rev > cur {
		check(err == mvcc.ErrFutureRev, "a future revision's read did not fail with ErrFutureRev")
		check(res != nil && len(res.KVs) == 0 && res.Count == -1 && res.Rev == cur,
			"a future revision's read returned a result")
		return
	}
	rev := q.ro.Rev
	if rev <= 0 {
		rev = cur
	}
	if rev < compacted {
		check(err == mvcc.ErrCompacted, "a compacted revision's read did not fail with ErrCompacted")
		check(res != nil && len(res.KVs) == 0 && res.Count == -1 && res.Rev == 0,
			"a compacted revision's read returned a result")
		return
	}
	check(err == nil, "a read failed")
	check(res != nil && res.Rev == cur, "a read's revision is not the store's")
	st := states[rev]
	var match []string
	for _, k := range keys {
		if _, ok := st[k]; ok && q.inRange(k) {
			match = append(match, k)
		}
	}
	n := len(match)
	if q.ro.CountOnly {
		check(len(res.KVs) == 0 && res.Count == n, "a count-only read's count is wrong")
		return
	}
	taken := n
	if q.ro.Limit > 0 && int(q.ro.Limit) < n {
		taken = int(q.ro.Limit)
	}
	total := n
	if q.ro.Limit > 0 && !q.ro.WithTotalCount && q.end != nil {
		total = taken
	}
	check(res.Count == total, "a read's count is wrong")
	check(len(res.KVs) == taken, "a read returned the wrong number of key-values")
	for i := 0; i < taken; i++ {
		checkKV(res.KVs[i], match[i], st[match[i]], q.ro.FastKeysOnly)
	}
}

func checkKV(kv *mvccpb.KeyValue, k string, e rec, keysOnly bool) {
	check(string(kv.Key) == k, "a read returned the wrong key")
	check(kv.CreateRevision == e.create, "a read returned the wrong create revision")
	check(kv.ModRevision == e.mod, "a read returned the wrong mod revision")
	check(kv.Version == e.ver, "a read returned the wrong version")
	check(kv.Lease == 0, "a read returned a lease")
	if keysOnly {
		check(len(kv.Value) == 0, "a keys-only read returned a value")
	} else {
		check(string(kv.Value) == e.val, "a read returned the wrong value")
	}
}

// A pending transaction's model: its state and whether it changed anything.
type pending struct {
	st      map[string]rec
	changed bool
}

func (p *pending) put(rev int64, k, v string) {
	e, ok := p.st[k]
	if ok {
		p.st[k] = rec{val: v, create: e.create, mod: rev, ver: e.ver + 1}
	} else {
		p.st[k] = rec{val: v, create: rev, mod: rev, ver: 1}
	}
	p.changed = true
}

// del deletes the range's keys and returns how many it deleted.
func (p *pending) del(q rangeReq) int64 {
	var n int64
	for _, k := range keys {
		if _, ok := p.st[k]; ok && q.inRange(k) {
			delete(p.st, k)
			n++
		}
	}
	if n > 0 {
		p.changed = true
	}
	return n
}

// commit appends the transaction's revision, if it changed anything.
func (m *model) commit(p *pending) {
	if p.changed {
		m.states = append(m.states, p.st)
	}
}

func (m *model) begin() *pending {
	return &pending{st: copyState(m.states[m.cur()])}
}

// writeTxn runs a write transaction of one to three puts and range deletes, with range reads
// between them.
func (t *tester) writeTxn() {
	m := t.m
	beginRev := m.cur()
	p := m.begin()
	tw := t.s.Write(traceutil.TODO())
	check(tw.Rev() == beginRev, "a write transaction's revision is not the store's")
	nops := 1 + t.r.intn(3)
	for i := 0; i < nops; i++ {
		if t.r.intn(3) == 0 {
			// a read of the pending state: the transaction's revision is the pending one once it
			// has a change
			cur := beginRev
			states := m.states
			if p.changed {
				cur = beginRev + 1
				states = append(m.states[:len(m.states):len(m.states)], p.st)
			}
			q := t.r.genRange(cur)
			res, err := tw.Range(context.TODO(), q.key, q.end, q.ro)
			checkRange(states, cur, m.compacted, q, res, err)
		}
		if t.r.intn(5) < 3 {
			k := t.r.genKey()
			t.vals++
			v := "v" + itoa(t.vals)
			p.put(beginRev+1, string(k), v)
			rev := tw.Put(k, []byte(v), lease.NoLease)
			check(rev == beginRev+1, "a put's revision is not the pending one")
		} else {
			q := rangeReq{key: t.r.genKey(), end: t.r.genEnd()}
			wantN := p.del(q)
			n, rev := tw.DeleteRange(q.key, q.end)
			check(n == wantN, "a range delete deleted the wrong number of keys")
			if p.changed {
				check(rev == beginRev+1, "a range delete's revision is not the pending one")
			} else {
				check(rev == beginRev, "a range delete of nothing has a revision")
			}
		}
	}
	check(len(tw.Changes()) > 0 == p.changed, "a write transaction's changes are wrong")
	tw.End()
	m.commit(p)
	check(t.s.Rev() == m.cur(), "the store's revision is wrong after a write transaction")
}

// viewWrite runs the store's own Put or DeleteRange.
func (t *tester) viewWrite() {
	m := t.m
	beginRev := m.cur()
	p := m.begin()
	if t.r.intn(2) == 0 {
		k := t.r.genKey()
		t.vals++
		v := "v" + itoa(t.vals)
		p.put(beginRev+1, string(k), v)
		rev := t.s.Put(k, []byte(v), lease.NoLease)
		check(rev == beginRev+1, "the store's put's revision is not the next one")
	} else {
		q := rangeReq{key: t.r.genKey(), end: t.r.genEnd()}
		wantN := p.del(q)
		n, rev := t.s.DeleteRange(q.key, q.end)
		check(n == wantN, "the store's range delete deleted the wrong number of keys")
		if p.changed {
			check(rev == beginRev+1, "the store's range delete's revision is not the next one")
		} else {
			check(rev == beginRev, "the store's range delete of nothing has a revision")
		}
	}
	m.commit(p)
	check(t.s.Rev() == m.cur(), "the store's revision is wrong after a write")
}

// read runs one to three range reads in a read transaction, or one through the store's Range.
func (t *tester) read() {
	m := t.m
	if t.r.intn(3) == 0 {
		q := t.r.genRange(m.cur())
		res, err := t.s.Range(context.TODO(), q.key, q.end, q.ro)
		checkRange(m.states, m.cur(), m.compacted, q, res, err)
		return
	}
	mode := mvcc.ConcurrentReadTxMode
	if t.r.intn(2) == 0 {
		mode = mvcc.SharedBufReadTxMode
	}
	tr := t.s.Read(mode, traceutil.TODO())
	check(tr.Rev() == m.cur(), "a read transaction's revision is not the store's")
	nr := 1 + t.r.intn(3)
	for i := 0; i < nr; i++ {
		q := t.r.genRange(m.cur())
		res, err := tr.Range(context.TODO(), q.key, q.end, q.ro)
		checkRange(m.states, m.cur(), m.compacted, q, res, err)
	}
	tr.End()
}

// compact runs a compaction and waits for its job: at a revision above the compaction revision,
// at or below it, or past the current one.
func (t *tester) compact() {
	m := t.m
	cur := m.cur()
	switch t.r.intn(5) {
	case 0:
		if m.compacted < 0 {
			return
		}
		rev := int64(t.r.intn(int(m.compacted) + 1))
		ch, err := t.s.Compact(traceutil.TODO(), rev)
		check(err == mvcc.ErrCompacted, "a compaction at or below the compaction revision did not fail")
		<-ch
	case 1:
		rev := cur + 1 + int64(t.r.intn(3))
		ch, err := t.s.Compact(traceutil.TODO(), rev)
		check(err == mvcc.ErrFutureRev && ch == nil, "a compaction past the current revision did not fail")
	default:
		if m.compacted >= cur {
			return
		}
		// the current revision half the time (as etcd's revision compactor's `Rev() -
		// retention` with no retention), else a revision above the compaction revision
		rev := cur
		if t.r.intn(2) == 0 {
			rev = m.compacted + 1 + int64(t.r.intn(int(cur-m.compacted)))
		}
		ch, err := t.s.Compact(traceutil.TODO(), rev)
		check(err == nil, "a compaction failed")
		<-ch
		m.compacted = rev
	}
	check(t.s.Rev() == cur, "a compaction changed the store's revision")
}

type tester struct {
	s    mvcc.KV
	m    *model
	r    *rng
	vals int
}

// itoa is strconv.Itoa of a non-negative number.
func itoa(n int) string {
	if n == 0 {
		return "0"
	}
	var b []byte
	for n > 0 {
		b = append([]byte{byte('0' + n%10)}, b...)
		n /= 10
	}
	return string(b)
}

// Run runs cfg.Ops random operations against a store over a new backend at cfg.Path, checking
// each against the model; it panics if a check fails.
func Run(cfg Config) {
	lg := zap.NewNop()
	bcfg := backend.DefaultBackendConfig(lg)
	bcfg.Path = cfg.Path
	be := backend.New(bcfg)
	s := mvcc.NewStore(lg, be, &lease.FakeLessor{}, mvcc.StoreConfig{})
	t := &tester{s: s, m: newModel(), r: &rng{s: cfg.Seed}}
	check(s.Rev() == 1, "a new store's revision is not 1")
	for i := 0; i < cfg.Ops; i++ {
		switch t.r.intn(10) {
		case 0, 1, 2:
			t.writeTxn()
		case 3:
			t.viewWrite()
		case 4, 5, 6, 7:
			t.read()
		default:
			t.compact()
		}
	}
	check(s.Close() == nil, "the store's close failed")
	check(be.Close() == nil, "the backend's close failed")
}

// Main runs 2000 operations from seed 1 against a store over a backend in the file mvccrand.db
// (which must not exist: the model starts empty), and panics if a check fails.
func Main() {
	Run(Config{Path: "mvccrand.db", Seed: 1, Ops: 2000})
}
