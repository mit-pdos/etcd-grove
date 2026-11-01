// Package mvccrand is a randomized tester of etcd's mvcc store, used the way etcd's server uses
// it, each result checked against a reference model. Run panics if a check fails.
//
// The configuration is the server's: the watchable store (mvcc.New) over a backend in a fresh
// file, a real lessor (lease.NewLessor over the same backend), and a post-lock hook installed on
// the backend after the store is made (the server's consistent-index save,
// getTxPostLockInsideApplyHook: it records the index being applied).
//
// The goroutines are the server's:
//   - one writer, the apply thread: write transactions as the server's txn package makes them
//     (Put and DeleteRange, each reading the previous key-values in the write transaction first;
//     Txn: its compares in a read transaction, shared-buffer or concurrent, then a write
//     transaction, which must start at the revision the read saw, running ranges that see its
//     pending changes, or a read-only transaction when it has no write), lease grants and revokes
//     (the revoke deletes the lease's keys through mvcc's range deleter, in one revision), puts
//     with a lease, Commit, and reads of its own; it publishes each revision it has written (the
//     applied index). Being the only writer, it knows every revision exactly.
//   - readers, the request goroutines: read transactions (Read in the concurrent mode),
//     read-only transactions (NewReadOnlyTxnWrite) and Rev, at the current revision, a past one or
//     a future one, each seeing at least the revision the writer had published before it started
//     (a linearizable read's floor) or none (a serializable read).
//   - a watch stream's two goroutines: one registers watchers (Watch, from an explicit start
//     revision, past or future, over a key, a range or a from-key range) and asks for progress
//     (RequestProgress, RequestProgressAll) as the writer goes on; the other receives the
//     responses (Chan). Each watcher's events must be exactly the model's changes in its range
//     from its start revision on, in order, each response's revision at least its events', and a
//     progress response at P must come after every change up to P.
//
// Not exercised: compaction, the store's own Put/DeleteRange/Range, Restore and hashing, which
// etcd's proof does not rely on (notes/mvccrand.md).
package mvccrand

import (
	"context"
	"sort"
	"sync"
	"sync/atomic"
	"time"

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

// A Config is a run's: the backend's file (fresh), the seed, the writer's number of operations,
// the readers and their reads each, the watchers, and how long to wait at the end for every
// watcher to have received every event (0: not at all; the check is then only of what arrived).
type Config struct {
	Path     string
	Seed     uint64
	Ops      int
	Readers  int
	Reads    int
	Watchers int
	Drain    time.Duration
}

// A Report is what a run observed beyond its checks: whether every watcher received every event
// up to the last revision (checked only with Config.Drain), how many events arrived, and how many
// reads saw a revision above the floor they started with (a write ended during the read's start).
type Report struct {
	WatchersComplete bool
	Events           int
	ReadsAboveFloor  int64
}

func check(ok bool, msg string) {
	if !ok {
		panic("mvccrand: " + msg)
	}
}

// A rec is a key's key-value in the model.
type rec struct {
	val    string
	create int64
	mod    int64
	ver    int64
	lease  int64
}

// A change is one change of a revision, as a watcher sees it: a put of the key-value kv, or a
// delete of key.
type change struct {
	del bool
	key string
	kv  rec
}

// A history is the store's expected history, shared by the writer (which appends) and the other
// goroutines: states[r] is the state at revision r (the store starts at revision 1, empty;
// states[0] is empty too, never read) and changes[r] its changes in order. A revision is
// appended before the transaction that makes it ends, so every revision the store shows is in
// it. published is the last revision the writer has finished writing.
type history struct {
	mu         sync.RWMutex
	states     []map[string]rec
	changes    [][]change
	published  atomic.Int64
	aboveFloor atomic.Int64
}

// seen checks that a read at revision cur is at least at its floor and at a revision written,
// and counts it if it is above its floor.
func (h *history) seen(floor, cur int64, what string) {
	check(floor <= cur, what+" is below a revision already written")
	check(cur < int64(len(h.snapshot())), what+" is at a revision not yet written")
	if floor > 0 && cur > floor {
		h.aboveFloor.Add(1)
	}
}

func newHistory() *history {
	h := &history{states: []map[string]rec{{}, {}}, changes: [][]change{nil, nil}}
	h.published.Store(1)
	return h
}

// snapshot returns the states so far (each state is never changed once appended).
func (h *history) snapshot() []map[string]rec {
	h.mu.RLock()
	defer h.mu.RUnlock()
	return h.states[:len(h.states):len(h.states)]
}

func (h *history) appendRev(st map[string]rec, chs []change) {
	h.mu.Lock()
	h.states = append(h.states, st)
	h.changes = append(h.changes, chs)
	h.mu.Unlock()
}

// changesAt returns revision r's changes; r must be in the history.
func (h *history) changesAt(r int64) []change {
	h.mu.RLock()
	defer h.mu.RUnlock()
	check(r < int64(len(h.changes)), "the store showed a revision the writer has not made")
	return h.changes[r]
}

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

// A rangeReq is a range read's request: [key, end), end nil for the key alone, empty for every
// key from key on.
type rangeReq struct {
	key []byte
	end []byte
	ro  mvcc.RangeOptions
}

// inRange says whether key k is in the range [key, end).
func inRange(key, end []byte, k string) bool {
	if end == nil {
		return k == string(key)
	}
	if k < string(key) {
		return false
	}
	return len(end) == 0 || k < string(end)
}

func (r *rng) genKey() []byte { return []byte(keys[r.intn(len(keys))]) }

// genEnd returns a range end: nil (one key) half the time, else empty (from key), an extra end
// or a key.
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

// genRange returns a range read's request for a transaction at revision cur: at the current
// revision (0 or negative), a past one, or cur + 1 (a future one).
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

// checkRange checks a range read's result (res, err) in a transaction at revision cur against
// the states (states[r] at revision r, for r up to cur). The store is never compacted.
func checkRange(states []map[string]rec, cur int64, q rangeReq, res *mvcc.RangeResult, err error) {
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
	check(err == nil, "a read failed")
	check(res != nil && res.Rev == cur, "a read's revision is not its transaction's")
	st := states[rev]
	var match []string
	for _, k := range keys {
		if _, ok := st[k]; ok && inRange(q.key, q.end, k) {
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
	if keysOnly {
		check(len(kv.Value) == 0, "a keys-only read returned a value")
	} else {
		check(string(kv.Value) == e.val, "a read returned the wrong value")
		check(kv.Lease == e.lease, "a read returned the wrong lease")
	}
}

func copyState(st map[string]rec) map[string]rec {
	c := make(map[string]rec, len(st))
	for k, v := range st {
		c[k] = v
	}
	return c
}

// A pending transaction's model: the revision it writes, its state and its changes.
type pending struct {
	rev     int64
	st      map[string]rec
	changes []change
}

func (p *pending) put(k, v string, l int64) {
	e, ok := p.st[k]
	if ok {
		p.st[k] = rec{val: v, create: e.create, mod: p.rev, ver: e.ver + 1, lease: l}
	} else {
		p.st[k] = rec{val: v, create: p.rev, mod: p.rev, ver: 1, lease: l}
	}
	p.changes = append(p.changes, change{key: k, kv: p.st[k]})
}

// del deletes the range's keys, in key order, and returns how many it deleted.
func (p *pending) del(key, end []byte) int64 {
	var n int64
	for _, k := range keys {
		if _, ok := p.st[k]; ok && inRange(key, end, k) {
			delete(p.st, k)
			p.changes = append(p.changes, change{del: true, key: k})
			n++
		}
	}
	return n
}

// The writer: the store, the lessor, the history, the model's live leases (the keys attached to
// each), the index being applied and the one the hook saw.
type writer struct {
	kv       mvcc.WatchableKV
	le       lease.Lessor
	h        *history
	r        *rng
	leases   map[int64]bool
	nextID   int64
	vals     int
	applying *atomic.Int64
	saved    *atomic.Int64
	ticks    chan int64
}

func (w *writer) cur() int64 { return w.h.published.Load() }

func (w *writer) begin() *pending {
	st := w.h.snapshot()
	cur := int64(len(st) - 1)
	check(cur == w.cur(), "the writer's history is ahead of its published revision")
	return &pending{rev: cur + 1, st: copyState(st[cur])}
}

// end appends the pending revision to the history (if it changed anything), runs the store's
// End, checks the store's revision and publishes it.
func (w *writer) end(p *pending, end func()) {
	if len(p.changes) > 0 {
		w.h.appendRev(p.st, p.changes)
	}
	end()
	want := p.rev - 1
	if len(p.changes) > 0 {
		want = p.rev
	}
	check(w.kv.Rev() == want, "the store's revision is not the writer's")
	w.h.published.Store(want)
}

// view returns the states with the pending revision appended (once it has a change) and the
// revision a read in the write transaction is at.
func (w *writer) view(p *pending) ([]map[string]rec, int64) {
	st := w.h.snapshot()
	if len(p.changes) == 0 {
		return st, p.rev - 1
	}
	return append(st, p.st), p.rev
}

// checkHook checks that the post-lock hook ran with the index being applied.
func (w *writer) checkHook(i int64) {
	check(w.saved.Load() == i, "the post-lock hook did not run in the write's lock")
}

func (w *writer) newVal() string {
	w.vals++
	return "v" + itoa(w.vals)
}

// genLease returns no lease half the time, else a live lease, if any.
func (w *writer) genLease() int64 {
	if w.r.intn(2) == 0 || len(w.leases) == 0 {
		return 0
	}
	var ids []int64
	for id := range w.leases {
		ids = append(ids, id)
	}
	sort.Slice(ids, func(i, j int) bool { return ids[i] < ids[j] })
	return ids[w.r.intn(len(ids))]
}

// writeOp runs one write operation inside the write transaction tw: a put, a range delete or a
// range read, each checked.
func (w *writer) writeOp(tw mvcc.TxnWrite, p *pending) {
	switch w.r.intn(3) {
	case 0:
		k := w.r.genKey()
		v := w.newVal()
		l := w.genLease()
		p.put(string(k), v, l)
		rev := tw.Put(k, []byte(v), lease.LeaseID(l))
		check(rev == p.rev, "a put's revision is not the pending one")
	case 1:
		key, end := w.r.genKey(), w.r.genEnd()
		n := p.del(key, end)
		gotN, rev := tw.DeleteRange(key, end)
		check(gotN == n, "a range delete deleted the wrong number of keys")
		if len(p.changes) > 0 {
			check(rev == p.rev, "a range delete's revision is not the pending one")
		} else {
			check(rev == p.rev-1, "a range delete in a transaction without changes has a revision")
		}
	default:
		states, cur := w.view(p)
		q := w.r.genRange(cur)
		res, err := tw.Range(context.TODO(), q.key, q.end, q.ro)
		checkRange(states, cur, q, res, err)
	}
}

// put is the server's txn.Put: a write transaction reading the key's previous key-value, then
// putting it.
func (w *writer) put(i int64) {
	p := w.begin()
	tw := w.kv.Write(traceutil.TODO())
	w.checkHook(i)
	check(tw.Rev() == p.rev-1, "a write transaction's revision is not the writer's")
	k := w.r.genKey()
	states, cur := w.view(p)
	q := rangeReq{key: k}
	res, err := tw.Range(context.TODO(), q.key, q.end, q.ro)
	checkRange(states, cur, q, res, err)
	v := w.newVal()
	l := w.genLease()
	p.put(string(k), v, l)
	check(tw.Put(k, []byte(v), lease.LeaseID(l)) == p.rev, "a put's revision is not the next one")
	w.end(p, tw.End)
}

// deleteRange is the server's txn.DeleteRange: a write transaction reading the range's previous
// key-values, then deleting them.
func (w *writer) deleteRange(i int64) {
	p := w.begin()
	tw := w.kv.Write(traceutil.TODO())
	w.checkHook(i)
	key, end := w.r.genKey(), w.r.genEnd()
	states, cur := w.view(p)
	q := rangeReq{key: key, end: end}
	res, err := tw.Range(context.TODO(), q.key, q.end, q.ro)
	checkRange(states, cur, q, res, err)
	n := p.del(key, end)
	gotN, rev := tw.DeleteRange(key, end)
	check(gotN == n, "a range delete deleted the wrong number of keys")
	if n > 0 {
		check(rev == p.rev, "a range delete's revision is not the next one")
	} else {
		check(rev == p.rev-1, "a range delete of nothing has a revision")
	}
	w.end(p, tw.End)
}

// txn is the server's txn.Txn: a compare in a read transaction (shared-buffer or concurrent),
// ended; then, with a write in the chosen branch, a write transaction at the same revision, else
// the read transaction made a read-only write transaction; the branch's operations in it.
func (w *writer) txn(i int64) {
	cur := w.cur()
	isWrite := w.r.intn(4) != 0
	mode := mvcc.ConcurrentReadTxMode
	if isWrite && w.r.intn(2) == 0 {
		mode = mvcc.SharedBufReadTxMode
	}
	tr := w.kv.Read(mode, traceutil.TODO())
	check(tr.Rev() == cur, "the writer's read transaction is not at its revision")
	check(tr.FirstRev() == -1, "a read transaction of a store never compacted has a first revision")
	k := w.r.genKey()
	states := w.h.snapshot()
	q := rangeReq{key: k}
	res, err := tr.Range(context.TODO(), q.key, q.end, q.ro)
	checkRange(states, cur, q, res, err)
	if !isWrite {
		tw := mvcc.NewReadOnlyTxnWrite(tr)
		nr := 1 + w.r.intn(3)
		for j := 0; j < nr; j++ {
			q := w.r.genRange(cur)
			res, err := tw.Range(context.TODO(), q.key, q.end, q.ro)
			checkRange(states, cur, q, res, err)
		}
		check(tw.Rev() == cur && len(tw.Changes()) == 0, "a read-only transaction changed something")
		tw.End()
		return
	}
	tr.End()
	p := w.begin()
	tw := w.kv.Write(traceutil.TODO())
	w.checkHook(i)
	check(tw.Rev() == cur, "a write after a read of the only writer is not at the read's revision")
	nops := 1 + w.r.intn(3)
	for j := 0; j < nops; j++ {
		w.writeOp(tw, p)
	}
	check((len(tw.Changes()) > 0) == (len(p.changes) > 0), "a write transaction's changes are wrong")
	w.end(p, tw.End)
}

// grant grants a new lease.
func (w *writer) grant(i int64) {
	w.nextID++
	id := w.nextID
	_, err := w.le.Grant(lease.LeaseID(id), 3600)
	check(err == nil, "a lease grant failed")
	w.checkHook(i)
	w.leases[id] = true
	check(w.kv.Rev() == w.cur(), "a lease grant made a revision")
}

// revoke revokes a live lease: its keys deleted in one revision, in key order.
func (w *writer) revoke(i int64) {
	id := w.genLease()
	if id == 0 {
		return
	}
	p := w.begin()
	var ks []string
	for _, k := range keys {
		if e, ok := p.st[k]; ok && e.lease == id {
			ks = append(ks, k)
		}
	}
	for _, k := range ks {
		delete(p.st, k)
		p.changes = append(p.changes, change{del: true, key: k})
	}
	w.end(p, func() {
		check(w.le.Revoke(lease.LeaseID(id)) == nil, "a lease revoke failed")
	})
	w.checkHook(i)
	delete(w.leases, id)
	check(w.le.Lookup(lease.LeaseID(id)) == nil, "a revoked lease is still there")
}

// checkLeases checks the lessor's record of the keys on each lease, which mvcc's puts and
// deletes keep: each key's lease is the model's, and each live lease has the model's keys.
func (w *writer) checkLeases() {
	st := w.h.snapshot()
	cur := st[len(st)-1]
	for _, k := range keys {
		var l int64
		if e, ok := cur[k]; ok {
			l = e.lease
		}
		check(int64(w.le.GetLease(lease.LeaseItem{Key: k})) == l, "the lessor has the wrong lease of a key")
	}
	for id := range w.leases {
		ls := w.le.Lookup(lease.LeaseID(id))
		check(ls != nil, "a live lease is gone")
		got := ls.Keys()
		sort.Strings(got)
		var want []string
		for _, k := range keys {
			if e, ok := cur[k]; ok && e.lease == id {
				want = append(want, k)
			}
		}
		check(len(got) == len(want), "a lease has the wrong number of keys")
		for j := range got {
			check(got[j] == want[j], "a lease has the wrong keys")
		}
	}
}

// read is the writer's own read: at exactly its revision (it is the only writer).
func (w *writer) read() {
	cur := w.cur()
	tr := w.kv.Read(mvcc.ConcurrentReadTxMode, traceutil.TODO())
	check(tr.Rev() == cur, "the only writer's read is not at its revision")
	states := w.h.snapshot()
	q := w.r.genRange(cur)
	res, err := tr.Range(context.TODO(), q.key, q.end, q.ro)
	checkRange(states, cur, q, res, err)
	tr.End()
}

// run runs ops operations, the i-th applying index i + 1, sending the published revision on
// ticks every ops / cap(ticks) operations (for the watch stream's registrations).
func (w *writer) run(ops int) {
	every := ops
	if cap(w.ticks) > 0 {
		every = ops/cap(w.ticks) + 1
	}
	for n := 0; n < ops; n++ {
		i := int64(n + 1)
		w.applying.Store(i)
		switch w.r.intn(20) {
		case 0, 1, 2, 3, 4:
			w.put(i)
		case 5, 6, 7:
			w.deleteRange(i)
		case 8, 9, 10, 11, 12, 13:
			w.txn(i)
		case 14:
			w.grant(i)
		case 15:
			w.revoke(i)
		case 16:
			w.kv.Commit()
		case 17:
			w.checkLeases()
		default:
			w.read()
		}
		if n%every == 0 && len(w.ticks) < cap(w.ticks) {
			w.ticks <- w.cur()
		}
	}
	close(w.ticks)
}

// reader runs reads concurrently with the writer: read transactions, read-only transactions and
// Rev, each at least at the revision published before it started (a linearizable read), or with
// no floor (a serializable read).
func reader(kv mvcc.WatchableKV, h *history, r *rng, reads int) {
	for n := 0; n < reads; n++ {
		floor := h.published.Load()
		if r.intn(4) == 0 {
			floor = 0
		}
		switch r.intn(4) {
		case 0:
			h.seen(floor, kv.Rev(), "Rev")
		case 1:
			tr := kv.Read(mvcc.ConcurrentReadTxMode, traceutil.TODO())
			tw := mvcc.NewReadOnlyTxnWrite(tr)
			cur := tw.Rev()
			h.seen(floor, cur, "a read-only transaction")
			states := h.snapshot()
			q := r.genRange(cur)
			res, err := tw.Range(context.TODO(), q.key, q.end, q.ro)
			checkRange(states, cur, q, res, err)
			check(len(tw.Changes()) == 0, "a read-only transaction has changes")
			tw.End()
		default:
			tr := kv.Read(mvcc.ConcurrentReadTxMode, traceutil.TODO())
			cur := tr.Rev()
			h.seen(floor, cur, "a read transaction")
			states := h.snapshot()
			check(tr.FirstRev() == -1, "a read transaction of a store never compacted has a first revision")
			nr := 1 + r.intn(3)
			for j := 0; j < nr; j++ {
				q := r.genRange(cur)
				res, err := tr.Range(context.TODO(), q.key, q.end, q.ro)
				checkRange(states, cur, q, res, err)
			}
			tr.End()
		}
	}
}

// A watcher's expectation: its range, and the position of its next event (revision rev, the
// index-th change of that revision in its range).
type watcher struct {
	key, end []byte
	rev      int64
	index    int
}

// A watchCheck holds the stream's watchers, by id, under a lock (the registering goroutine adds
// one, Watch included, under it, so the receiving goroutine knows a watcher before its events).
type watchCheck struct {
	mu       sync.Mutex
	h        *history
	watchers map[mvcc.WatchID]*watcher
	events   int
}

// expect returns the next change in w's range at or after its position, up to revision upto
// (false if there is none).
func (c *watchCheck) expect(w *watcher, upto int64) (change, int64, bool) {
	for r := w.rev; r <= upto; r++ {
		chs := c.h.changesAt(r)
		seen := 0
		for _, ch := range chs {
			if !inRange(w.key, w.end, ch.key) {
				continue
			}
			if r > w.rev || seen >= w.index {
				return ch, r, true
			}
			seen++
		}
	}
	return change{}, 0, false
}

// advance moves w past the change at revision r it just received.
func (w *watcher) advance(r int64) {
	if r > w.rev {
		w.rev, w.index = r, 0
	}
	w.index++
}

// receive checks a response: each event is its watcher's next expected change, at or below the
// response's revision; a response without events is progress, for one watcher after every
// change up to its revision. (A progress response for the whole stream, id -1, speaks for the
// watchers registered when it was made, which the receiver cannot tell apart from later ones:
// only its revision is checked.)
func (c *watchCheck) receive(resp mvcc.WatchResponse) {
	c.mu.Lock()
	defer c.mu.Unlock()
	check(resp.CompactRevision == 0, "a watch response reports a compaction")
	if len(resp.Events) == 0 {
		check(resp.Revision < int64(len(c.h.snapshot())), "a progress response is at a revision not yet written")
		if w := c.watchers[resp.WatchID]; w != nil {
			_, _, more := c.expect(w, resp.Revision)
			check(!more, "a progress response came before a change at or below its revision")
		}
		return
	}
	w := c.watchers[resp.WatchID]
	check(w != nil, "a watch response for an unknown watcher")
	for _, ev := range resp.Events {
		r := ev.Kv.ModRevision
		check(r <= resp.Revision, "a watch response's revision is below its event's")
		want, wr, ok := c.expect(w, r)
		check(ok && wr == r, "a watcher received an event it should not have, or missed one")
		check(string(ev.Kv.Key) == want.key, "a watch event has the wrong key")
		if want.del {
			check(ev.Type == mvccpb.Event_DELETE, "a watch event is not a delete")
			check(ev.Kv.CreateRevision == 0 && ev.Kv.Version == 0 && len(ev.Kv.Value) == 0,
				"a delete event carries a key-value")
		} else {
			check(ev.Type == mvccpb.Event_PUT, "a watch event is not a put")
			checkKV(ev.Kv, want.key, want.kv, false)
		}
		w.advance(r)
		c.events++
	}
}

// complete says whether every watcher has received every change up to revision upto.
func (c *watchCheck) complete(upto int64) bool {
	c.mu.Lock()
	defer c.mu.Unlock()
	for _, w := range c.watchers {
		if _, _, more := c.expect(w, upto); more {
			return false
		}
	}
	return true
}

// register registers a watcher on each tick (the writer's published revision), from a start
// revision up to one past it, and asks for progress now and then.
func (c *watchCheck) register(ws mvcc.WatchStream, r *rng, ticks chan int64) {
	for pub := range ticks {
		start := 1 + int64(r.intn(int(pub)+1))
		w := &watcher{key: r.genKey(), end: r.genEnd(), rev: start}
		c.mu.Lock()
		// id 0: the stream assigns one (clientv3.AutoWatchID, as etcd's client asks)
		id, err := ws.Watch(context.TODO(), mvcc.WatchID(0), w.key, w.end, start)
		if len(w.end) != 0 && string(w.end) <= string(w.key) {
			check(err == mvcc.ErrEmptyWatcherRange && id == -1, "a watch of an empty range did not fail")
			c.mu.Unlock()
			continue
		}
		check(err == nil, "a watch failed")
		c.watchers[id] = w
		c.mu.Unlock()
		switch r.intn(3) {
		case 0:
			ws.RequestProgress(id)
		case 1:
			ws.RequestProgressAll()
		}
	}
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

// Run runs a test of cfg: the store set up as etcd's server does, the writer, the readers and
// the watch stream concurrently; it panics if a check fails.
func Run(cfg Config) Report {
	lg := zap.NewNop()
	bcfg := backend.DefaultBackendConfig(lg)
	bcfg.Path = cfg.Path
	be := backend.New(bcfg)
	le := lease.NewLessor(lg, be, nil, lease.LessorConfig{MinLeaseTTL: 1})
	kv := mvcc.New(lg, be, le, mvcc.StoreConfig{})
	var applying, saved atomic.Int64
	be.SetTxPostLockInsideApplyHook(func() {
		if a := applying.Load(); a > saved.Load() {
			saved.Store(a)
		}
	})
	check(kv.Rev() == 1, "a new store's revision is not 1")

	h := newHistory()
	w := &writer{kv: kv, le: le, h: h, r: &rng{s: cfg.Seed}, leases: map[int64]bool{},
		applying: &applying, saved: &saved, ticks: make(chan int64, cfg.Watchers)}
	ws := kv.NewWatchStream()
	c := &watchCheck{h: h, watchers: map[mvcc.WatchID]*watcher{}}

	var recvDone sync.WaitGroup
	recvDone.Add(1)
	go func() {
		for resp := range ws.Chan() {
			c.receive(resp)
		}
		recvDone.Done()
	}()
	var wg sync.WaitGroup
	wg.Add(2 + cfg.Readers)
	go func() {
		w.run(cfg.Ops)
		wg.Done()
	}()
	go func() {
		c.register(ws, &rng{s: cfg.Seed ^ 0x5bd1e995}, w.ticks)
		wg.Done()
	}()
	for id := 0; id < cfg.Readers; id++ {
		r := &rng{s: cfg.Seed + uint64(id+1)*0x632be59bd9b4e019}
		go func() {
			reader(kv, h, r, cfg.Reads)
			wg.Done()
		}()
	}
	wg.Wait()

	last := h.published.Load()
	complete := c.complete(last)
	if cfg.Drain > 0 {
		deadline := time.Now().Add(cfg.Drain)
		for !complete && time.Now().Before(deadline) {
			time.Sleep(10 * time.Millisecond)
			complete = c.complete(last)
		}
	}
	ws.Close()
	recvDone.Wait()
	check(kv.Close() == nil, "the store's close failed")
	le.Stop()
	check(be.Close() == nil, "the backend's close failed")
	return Report{WatchersComplete: complete, Events: c.events, ReadsAboveFloor: h.aboveFloor.Load()}
}

// Main runs the writer's 1000 operations against 4 readers of 200 reads and 8 watchers, from seed
// 1, over a backend in the file mvccrand.db (which must not exist: the model starts empty), and
// panics if a check fails. It does not wait for the watchers to catch up (only what they
// received is checked).
func Main() {
	Run(Config{Path: "mvccrand.db", Seed: 1, Ops: 1000, Readers: 4, Reads: 200, Watchers: 8})
}
