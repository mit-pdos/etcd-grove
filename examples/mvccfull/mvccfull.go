// Package mvccfull is a tester of etcd's mvcc package meant to cover every execution of mvcc that
// etcd's server can produce, each result checked against a reference model, so that knowing
// Main never fails is knowing mvcc correct on every such execution (up to Main's sizes). It is
// not a bug search: a run is not tuned to find bugs fast, and it is not seeded.
//
// # Coverage
//
// Every choice the tester makes (which operation, which keys, values, leases, revisions, which
// member, when to compact, restart or restore, which watchers to register or cancel) comes from
// primitive.RandomUint64, which in Go is random and in GooseLang returns any value. So a theorem
// that Run(cfg) never fails, for every cfg, quantifies over every sequence of choices, every
// interleaving of the goroutines and every configuration: the executions it covers are all those
// of a two-member etcd cluster's use of mvcc, up to cfg's sizes (except the restrictions below).
//
// # Auditing
//
// What the checks say is in this file. config.go holds only what makes executions larger or more
// likely (sizes, mvcc's batch settings, the weights of the choices, sleeps), never what is
// checked: the auditor of the checks can skip it, and mvccfull_test.go, which picks Configs
// engineered to make classes of bugs likely. Main's Config reaches past mvcc's internal
// thresholds, so that the paths behind them are among its executions: more revisions than
// watchBatchMaxRevs (1000, an unsynced watcher catching up in batches) and than restoreChunkKeys
// (10000 entries, a restart restoring the index in chunks), values larger than a bbolt page,
// more keys than the index's B-tree degree, more events than a watch channel holds (chanBufLen,
// victims), compaction and backend batch limits of 1.
//
// # The system
//
// Two members, a leader and a follower, each as etcd's server sets one up: a backend in its own
// file (backend.New), a real lessor over it (lease.NewLessor), the watchable store (mvcc.New),
// and the post-lock hook installed on the backend after the store is made (the server's
// consistent-index save: it records the index being applied). One operation log: the leader
// applies each operation as it is made; the follower applies the same log, lagging behind.
//
// # The goroutines
//
//   - The writer, both members' apply loops: the only goroutine that writes, commits, compacts,
//     restores or restarts (etcd's apply loop is; nonissues/etcd-mvcc-progress-lock-order-deadlock
//     is the precondition this meets). Operations: Put and DeleteRange as the server's txn package
//     makes them (a range of the previous key-values in the write transaction first); Txn (its
//     compare in a shared-buffer read transaction then a write transaction at the read's
//     revision, or in the write transaction itself, or in a concurrent read transaction made a
//     read-only write transaction; then puts, deletes and ranges of the pending state, the puts'
//     keys distinct and outside the deletes' ranges, as etcd's checkIntervals requires); lease
//     grants, revokes (the lease's keys deleted in one revision through mvcc's range deleter) and
//     puts with a lease; Compact, at any revision (past the compaction revision, at or below it, in
//     the future), waiting for the compaction to finish or not; Commit; reads at the writer's own
//     revision; the lessor's record of each key's lease and each lease's keys. Member steps: the
//     follower applies some of the log; the follower installs a snapshot at the leader's point (a
//     backend opened on the snapshot's file, Lessor.Recover, Restore, the hook on the new backend,
//     the old backend closed: the server's applySnapshot; the file made by a third store applying
//     the log, then closed, in place of the leader's backend.Snapshot: an image of the same
//     history, which is all Restore's contract asks); a member
//     restarts (its watch streams drained and closed, the store, lessor and backend closed, then
//     reopened on the same file, possibly with another configuration: a resumed compaction, the
//     index and the leases restored from the file).
//   - Readers on each member, the request goroutines: Rev, FirstRev, read transactions, read-only
//     transactions, the store's own Range (as the watch server's previous key-value), each at
//     least at the revision the member had published before it started (a linearizable read) and
//     at most at one written; reads below the compaction revision fail with ErrCompacted, reads
//     past the current one with ErrFutureRev. And the corruption checker: HashByRev of a revision
//     on both members, and the compaction hashes (Hashes); two hashes of the same revision and
//     compaction revision must be equal.
//   - Watch streams on each member (two goroutines each, as the watch server's): one registers
//     watchers (from revision 0, i.e. from now; from a past, current or future revision; over a
//     key, a range or a from-key range; with the watch server's NoPut or NoDelete filter; the
//     stream picking the id, as etcd's client asks), cancels them, asks for progress
//     (RequestProgress, RequestProgressAll) and the stream's revision, and watches an empty range
//     (which must fail); the other receives the responses and, for some events, reads the key's
//     previous value as the watch server does (Range at the event's revision minus one).
//
// # The checks
//
// Only what mvcc's contract promises its clients (Spec/.../storage/mvcc/Api.lean, wsRecvOk):
// each watcher's events must be exactly the changes in its range (filtered) from its start
// revision on, in order, with every field, each in a response whose revision is at least its
// event's; a watcher's progress response at P must come after every such change up to P and be at
// least its start revision less one; a stream's progress response must come after those of every
// watcher not cancelled that registered before it was sent (which the receiver knows of the
// watchers registered before it last found the channel empty, recvOne); the revisions of the
// responses without events never decrease; a compaction response must name a revision compacted.
// When a
// stream is closed (at a restart, and at the end), every watcher not cancelled or compacted must
// have received every change up to the member's revision: the stream is drained first, so Main
// returns only if mvcc delivered every event (a liveness check that partial correctness can
// state: if Main returns, nothing was lost). At the end, both members are restarted once more and
// every revision not compacted is read in full on each: what the files hold is the history.
//
// # Restrictions
//
// Each excludes executions that reach a known bug of mvcc, and is lifted when the bug is fixed;
// they are the executions this tester does not cover (notes/mvccfull.md lists them with the
// rest of what is not covered):
//   - No compaction at revision 0 (issues/etcd-mvcc-hashbyrev-zero-stored.md,
//     issues/etcd-restore-scheduled-compact-zero.md).
//   - Fewer than 512 watchers per member (maxWatchersPerSync; issues/etcd-watch-compacted-resent.md).
//   - No negative compaction batch limit (nonissues/etcd-compaction-negative-batch-limit.md).
//   - Restarts are clean (the store, lessor and backend closed): no crash.
//   - No full-store Hash() (issues/etcd-mvcc-hash-currentrev-race.md, fixed upstream after the pin).
//   - HashByRev's stored-hash path is not checked for its current revision
//     (issues/etcd-mvcc-hashbyrev-restore-rev1.md).
//   - The writer waits for a compaction only before its next step
//     (issues/etcd-restore-pending-compaction-unclosed.md).
//   - Two members' hashes of a revision at which no key is live need not be equal
//     (issues/etcd-mvcc-compact-hash-empty-keyspace.md, the compaction hash against a lagging
//     member's; issues/etcd-mvcc-hashkv-during-compaction-empty-keyspace.md, a hash during a
//     compaction: the corruption checker's false alarms).
package mvccfull

import (
	"context"
	"sort"
	"sync"
	"sync/atomic"
	"time"

	"github.com/Masterminds/semver/v3"
	"go.uber.org/zap"

	"go.etcd.io/etcd/api/v3/mvccpb"
	"go.etcd.io/etcd/pkg/v3/traceutil"
	"go.etcd.io/etcd/server/v3/lease"
	"go.etcd.io/etcd/server/v3/storage/backend"
	"go.etcd.io/etcd/server/v3/storage/mvcc"
)

// A Report counts what a run exercised beyond its checks.
type Report struct {
	Revisions   int64
	Events      int64
	Progress    int64
	Compacted   int64
	Cancels     int64
	Reads       int64
	HashPairs   int64
	Compactions int64
	Restores    int64
	Restarts    int64
}

func check(ok bool, msg string) {
	if !ok {
		panic("mvccfull: " + msg)
	}
}

// walkKeys appends the strings over a, b, c that extend p, up to length depth, in increasing
// order (p first).
func walkKeys(ks []string, p string, depth int) []string {
	if len(p) > 0 {
		ks = append(ks, p)
	}
	if len(p) == depth {
		return ks
	}
	ks = walkKeys(ks, p+"a", depth)
	ks = walkKeys(ks, p+"b", depth)
	return walkKeys(ks, p+"c", depth)
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

// ---------------------------------------------------------------------------------------------
// The model

// A kvRec is a key's key-value in the model.
type kvRec struct {
	val    string
	create int64
	mod    int64
	ver    int64
	lease  int64
}

// A change is one change of a revision: a put of the key-value kv, or a delete of key.
type change struct {
	del bool
	key string
	kv  kvRec
}

// A history is the log's history, shared by every goroutine: states[r] is the state at revision
// r (revision 1 is the empty store; states[0] is empty too and never read), changes[r] its
// changes in order, and comps the revisions of the log's successful compactions, in order. The
// leader appends a revision before the transaction that makes it ends, so every revision a
// member shows is in it.
type history struct {
	mu      sync.RWMutex
	states  []map[string]kvRec
	changes [][]change
	comps   []int64
}

func (h *history) snapshot() []map[string]kvRec {
	h.mu.RLock()
	defer h.mu.RUnlock()
	return h.states[:len(h.states):len(h.states)]
}

func (h *history) appendRev(st map[string]kvRec, chs []change) {
	h.mu.Lock()
	h.states = append(h.states, st)
	h.changes = append(h.changes, chs)
	h.mu.Unlock()
}

// changesAt returns revision r's changes; r must be in the history.
func (h *history) changesAt(r int64) []change {
	h.mu.RLock()
	defer h.mu.RUnlock()
	check(r < int64(len(h.changes)), "a member showed a revision not yet written")
	return h.changes[r]
}

func (h *history) addComp(c int64) {
	h.mu.Lock()
	h.comps = append(h.comps, c)
	h.mu.Unlock()
}

// compPrev says whether c is a revision the log compacted at, and the compaction revision before
// it (-1 for the first).
func (h *history) compPrev(c int64) (int64, bool) {
	h.mu.RLock()
	defer h.mu.RUnlock()
	prev := int64(-1)
	for _, x := range h.comps {
		if x == c {
			return prev, true
		}
		prev = x
	}
	return 0, false
}

func copyState(st map[string]kvRec) map[string]kvRec {
	c := make(map[string]kvRec, len(st))
	for k, v := range st {
		c[k] = v
	}
	return c
}

// inRange says whether key k is in the range [key, end): end nil is the key alone, end empty
// every key from key on.
func inRange(key, end []byte, k string) bool {
	if end == nil {
		return k == string(key)
	}
	if len(end) == 0 {
		return k >= string(key)
	}
	return string(key) <= k && k < string(end)
}

// A pending transaction's model: the revision it writes, its state and its changes.
type pending struct {
	rev     int64
	st      map[string]kvRec
	changes []change
}

func (p *pending) put(k, v string, l int64) {
	e, ok := p.st[k]
	if ok {
		p.st[k] = kvRec{val: v, create: e.create, mod: p.rev, ver: e.ver + 1, lease: l}
	} else {
		p.st[k] = kvRec{val: v, create: p.rev, mod: p.rev, ver: 1, lease: l}
	}
	p.changes = append(p.changes, change{key: k, kv: p.st[k]})
}

// del deletes the range's keys, in key order, and returns how many it deleted.
func (p *pending) del(keys []string, key, end []byte) int64 {
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

// A rangeReq is a range read's request.
type rangeReq struct {
	key []byte
	end []byte
	ro  mvcc.RangeOptions
}

// checkRangeAt checks a range read's result (res, err) in a transaction at revision cur of a
// store compacted at cmp, against the states (states[r] at revision r, for r up to cur).
func checkRangeAt(keys []string, states []map[string]kvRec, cur, cmp int64, q rangeReq, res *mvcc.RangeResult, err error) {
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
	if rev < cmp {
		check(err == mvcc.ErrCompacted, "a compacted revision's read did not fail with ErrCompacted")
		check(res != nil && len(res.KVs) == 0 && res.Count == -1 && res.Rev == 0,
			"a compacted revision's read returned a result")
		return
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

func checkKV(kv *mvccpb.KeyValue, k string, e kvRec, keysOnly bool) {
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

// ---------------------------------------------------------------------------------------------
// The members

// A member is one etcd member's storage: its file, its backend, lessor and store, the post-lock
// hook's record (the index being applied, and the last one the hook saw), and its watch streams.
// The writer's model of it: the log operations it has applied, its revision, compaction revision
// and live leases (in increasing order). For the other goroutines, bounds: the member's store
// shows a revision in [revLo, revHi] and a compaction revision in [cmpLo, cmpHi] (each lo stored
// after a step, each hi before).
type member struct {
	id       int
	path     string
	be       backend.Backend
	le       lease.Lessor
	kv       mvcc.WatchableKV
	hook     func()
	applying atomic.Int64
	saved    atomic.Int64
	revLo    atomic.Int64
	revHi    atomic.Int64
	cmpLo    atomic.Int64
	cmpHi    atomic.Int64
	regs     atomic.Int64
	streams  []*stream

	ops    int
	rev    int64
	cmp    int64
	leases []int64
}

type noCluster struct{}

func (noCluster) Version() *semver.Version { return nil }

// An op is one operation of the log, with every choice made (so that the follower applies the
// leader's operation).
type op struct {
	kind   int
	key    []byte
	end    []byte
	val    string
	lease  int64
	q      rangeReq
	write  bool
	shared bool
	subs   []subOp
	id     int64
	rev    int64
	wait   bool
}

const (
	opPut = iota
	opDelete
	opTxn
	opGrant
	opRevoke
	opCompact
	opCommit
	opRead
	opLeases
)

// A subOp is one operation of a transaction: a put (0), a range delete (1) or a range read (2).
type subOp struct {
	kind  int
	key   []byte
	end   []byte
	val   string
	lease int64
	q     rangeReq
}

// The runner: the configuration, the keys, the history, the members (0 the leader, 1 the
// follower), the log, and the model's counters.
type runner struct {
	cfg       Config
	keys      []string
	lg        *zap.Logger
	h         *history
	ms        []*member
	log       []*op
	nextLease int64
	vals      int
	builds    int
	readStop  atomic.Int64
	readWg    sync.WaitGroup

	revisions, events, progress, compacted, cancels, reads, hashPairs, compactions,
	restores, restarts atomic.Int64
}

// memberPath is the file of member id (0 the leader, 1 the follower), buildPath the file of the
// n-th snapshot builder (restore): FilePaths lists them.
func memberPath(prefix string, id int) string { return prefix + "-" + itoa(id) + ".db" }

func buildPath(prefix string, n int) string { return prefix + "-b" + itoa(n) + ".db" }

// FilePaths is every file a run of cfg may create (absent at its start): the two members' and one
// per snapshot install, at most one per writer step.
func FilePaths(cfg Config) []string {
	ps := []string{memberPath(cfg.Prefix, 0), memberPath(cfg.Prefix, 1)}
	for n := 1; n <= cfg.Ops; n++ {
		ps = append(ps, buildPath(cfg.Prefix, n))
	}
	return ps
}

// openBackend opens a backend on path, with the configuration's batch settings.
func (x *runner) openBackend(path string) backend.Backend {
	bcfg := backend.DefaultBackendConfig(x.lg)
	bcfg.Path = path
	if x.cfg.BatchLimit > 0 {
		bcfg.BatchLimit = x.cfg.BatchLimit
	}
	if x.cfg.BatchInterval > 0 {
		bcfg.BatchInterval = x.cfg.BatchInterval
	}
	return backend.New(bcfg)
}

// open opens m's backend, lessor and store on its file, as the server does, and checks the store
// against the model.
func (x *runner) open(m *member) {
	m.be = x.openBackend(m.path)
	m.le = lease.NewLessor(x.lg, m.be, noCluster{}, lease.LessorConfig{MinLeaseTTL: 1})
	scfg := mvcc.StoreConfig{CompactionSleepInterval: x.cfg.CompactionSleep}
	if x.cfg.CompactionBatchLimit > 0 {
		scfg.CompactionBatchLimit = x.cfg.CompactionBatchLimit
	}
	m.kv = mvcc.New(x.lg, m.be, m.le, scfg)
	m.be.SetTxPostLockInsideApplyHook(m.hook)
	check(m.kv.Rev() == m.rev, "an opened store's revision is not the file's")
	tr := m.kv.Read(mvcc.ConcurrentReadTxMode, traceutil.TODO())
	check(tr.Rev() == m.rev && tr.FirstRev() == m.cmp, "an opened store's compaction revision is not the file's")
	tr.End()
	x.checkLeases(m)
}

// shut closes m's store, lessor and backend.
func (x *runner) shut(m *member) {
	check(m.kv.Close() == nil, "a store's close failed")
	m.le.Stop()
	check(m.be.Close() == nil, "a backend's close failed")
}

// newMember opens a member over a fresh file.
func (x *runner) newMember(id int, path string) *member {
	m := &member{id: id, path: path, rev: 1, cmp: -1}
	m.hook = func() {
		if a := m.applying.Load(); a > m.saved.Load() {
			m.saved.Store(a)
		}
	}
	m.revLo.Store(1)
	m.revHi.Store(1)
	m.cmpLo.Store(-1)
	m.cmpHi.Store(-1)
	x.open(m)
	return m
}

// restart stops the readers and drains and closes m's watch streams (a restart is the member's
// process restarting: its requests in flight end with it), closes m and opens it again on its
// file, and starts them again.
func (x *runner) restart(m *member) {
	x.stopReaders()
	x.endEpoch(m)
	x.shut(m)
	x.open(m)
	x.restarts.Add(1)
	x.startEpoch(m)
	x.startReaders()
}

// restore installs a snapshot on the follower f at the leader l's point of the log, as the
// server's applySnapshot does (a backend opened on the snapshot's file, the lessor recovered from
// it, the store restored on it, the hook installed on it, the old backend closed). The snapshot's
// file is made by a third store, the builder: a fresh member applying the log up to l's point,
// then closed (the file then holds an image of that history, as a leader's backend snapshot
// does; Restore takes any image of a history extending the store's).
func (x *runner) restore(l, f *member) {
	x.builds++
	b := x.newMember(2, buildPath(x.cfg.Prefix, x.builds))
	for b.ops < l.ops {
		x.apply(b, x.log[b.ops], false)
	}
	x.shut(b)

	f.revHi.Store(b.rev)
	f.cmpHi.Store(b.cmp)
	newbe := x.openBackend(b.path)
	kv := f.kv
	f.le.Recover(newbe, func() lease.TxnDelete { return kv.Write(traceutil.TODO()) })
	check(f.kv.Restore(newbe) == nil, "a restore failed")
	newbe.SetTxPostLockInsideApplyHook(f.hook)
	oldbe := f.be
	f.be = newbe
	f.path = b.path
	check(oldbe.Close() == nil, "the old backend's close failed")

	f.ops, f.rev, f.cmp = b.ops, b.rev, b.cmp
	f.leases = append([]int64(nil), b.leases...)
	f.revLo.Store(f.rev)
	f.cmpLo.Store(f.cmp)
	check(f.kv.Rev() == f.rev, "a restored store's revision is not the snapshot's")
	tr := f.kv.Read(mvcc.ConcurrentReadTxMode, traceutil.TODO())
	check(tr.FirstRev() == f.cmp, "a restored store's compaction revision is not the snapshot's")
	tr.End()
	x.checkLeases(f)
	x.restores.Add(1)
}

// checkLeases checks m's lessor against the model: each key's lease, each live lease's keys, and
// no other lease.
func (x *runner) checkLeases(m *member) {
	st := x.h.snapshot()[m.rev]
	for _, k := range x.keys {
		var l int64
		if e, ok := st[k]; ok {
			l = e.lease
		}
		check(int64(m.le.GetLease(lease.LeaseItem{Key: k})) == l, "the lessor has the wrong lease of a key")
	}
	check(len(m.le.Leases()) == len(m.leases), "the lessor has the wrong leases")
	for _, id := range m.leases {
		ls := m.le.Lookup(lease.LeaseID(id))
		check(ls != nil, "a live lease is gone")
		got := ls.Keys()
		sort.Strings(got)
		var want []string
		for _, k := range x.keys {
			if e, ok := st[k]; ok && e.lease == id {
				want = append(want, k)
			}
		}
		check(len(got) == len(want), "a lease has the wrong number of keys")
		for j := range got {
			check(got[j] == want[j], "a lease has the wrong keys")
		}
	}
}

// ---------------------------------------------------------------------------------------------
// The log's operations

func (x *runner) genKey() []byte { return []byte(x.keys[choose(len(x.keys))]) }

// genEnd returns a range end: nil (one key), empty (from the key on), past every key, or a key.
func (x *runner) genEnd() []byte {
	switch choose(4) {
	case 0:
		return nil
	case 1:
		return []byte{}
	case 2:
		return []byte("d")
	default:
		return x.genKey()
	}
}

// genRange returns a range read's request for a transaction at revision cur of a member whose
// compaction revision is cmp: at the current revision (0 or negative), any revision up to cur + 1
// (compacted, past, current, future), any limit up to past the number of keys (0: none), any
// count-only, keys-only and total-count options.
func (x *runner) genRange(cur, cmp int64) rangeReq {
	q := rangeReq{key: x.genKey(), end: x.genEnd()}
	switch pick(x.cfg.Mix.RangeRev, 4) {
	case 0:
		q.ro.Rev = 0
	case 1:
		q.ro.Rev = -1
	case 2:
		q.ro.Rev = int64(choose(int(cur) + 2))
	default:
		q.ro.Rev = cmp
	}
	q.ro.Limit = int64(choose(len(x.keys) + 2))
	q.ro.CountOnly = choose(2) == 0
	q.ro.FastKeysOnly = choose(2) == 0
	q.ro.WithTotalCount = choose(2) == 0
	return q
}

// newVal returns a new value, of any length up to MaxVal.
func (x *runner) newVal() string {
	x.vals++
	pad := make([]byte, choose(x.cfg.MaxVal+1))
	for i := range pad {
		pad[i] = 'x'
	}
	return "v" + itoa(x.vals) + string(pad)
}

// genLease returns no lease half the time, else a live lease of m, if any.
func (x *runner) genLease(m *member) int64 {
	if choose(2) == 0 || len(m.leases) == 0 {
		return 0
	}
	return m.leases[choose(len(m.leases))]
}

// genSubs returns a write transaction's operations, as etcd's checkIntervals allows them: the
// puts' keys distinct, and none in a delete's range.
func (x *runner) genSubs(m *member) []subOp {
	n := 1 + choose(3)
	var subs []subOp
	var puts []string
	var dels []subOp
	for j := 0; j < n; j++ {
		switch choose(3) {
		case 0:
			k := x.genKey()
			ok := true
			for _, p := range puts {
				if p == string(k) {
					ok = false
				}
			}
			for _, d := range dels {
				if inRange(d.key, d.end, string(k)) {
					ok = false
				}
			}
			if ok {
				puts = append(puts, string(k))
				subs = append(subs, subOp{kind: 0, key: k, val: x.newVal(), lease: x.genLease(m)})
			}
		case 1:
			d := subOp{kind: 1, key: x.genKey(), end: x.genEnd()}
			ok := true
			for _, p := range puts {
				if inRange(d.key, d.end, p) {
					ok = false
				}
			}
			if ok {
				dels = append(dels, d)
				subs = append(subs, d)
			}
		default:
			subs = append(subs, subOp{kind: 2, q: x.genRange(m.rev+1, m.cmp)})
		}
	}
	return subs
}

// gen returns the next operation of the log, made for the leader l.
func (x *runner) gen(l *member) *op {
	switch pick(x.cfg.Mix.Op, 9) {
	case opPut:
		return &op{kind: opPut, key: x.genKey(), val: x.newVal(), lease: x.genLease(l)}
	case opDelete:
		return &op{kind: opDelete, key: x.genKey(), end: x.genEnd()}
	case opTxn:
		o := &op{kind: opTxn, q: rangeReq{key: x.genKey()}, write: choose(2) == 0}
		if o.write {
			o.shared = choose(2) == 0
			o.subs = x.genSubs(l)
		} else {
			nr := 1 + choose(3)
			for j := 0; j < nr; j++ {
				o.subs = append(o.subs, subOp{kind: 2, q: x.genRange(l.rev, l.cmp)})
			}
		}
		return o
	case opGrant:
		x.nextLease++
		return &op{kind: opGrant, id: x.nextLease}
	case opRevoke:
		if len(l.leases) == 0 {
			return &op{kind: opCommit}
		}
		return &op{kind: opRevoke, id: l.leases[choose(len(l.leases))]}
	case opCompact:
		// at any revision from 1 (not 0: the restriction) to one past the current one; at one
		// above the compaction revision; or at the current revision
		o := &op{kind: opCompact, rev: 1 + int64(choose(int(l.rev)+1)), wait: choose(2) == 0}
		switch pick(x.cfg.Mix.CompactAt, 3) {
		case 1:
			o.rev = l.cmp + 1
			if o.rev < 1 {
				o.rev = 1
			}
		case 2:
			o.rev = l.rev
		}
		return o
	case opCommit:
		return &op{kind: opCommit}
	case opRead:
		return &op{kind: opRead, q: x.genRange(l.rev, l.cmp)}
	default:
		return &op{kind: opLeases}
	}
}

// apply applies the operation o to m (lead: m is the leader, which appends o's revision to the
// history; the follower finds it there), checking every result.
func (x *runner) apply(m *member, o *op, lead bool) {
	m.ops++
	i := int64(m.ops)
	m.applying.Store(i)
	switch o.kind {
	case opPut:
		p := x.begin(m)
		tw := m.kv.Write(traceutil.TODO())
		x.checkHook(m, i)
		check(tw.Rev() == m.rev, "a write transaction's revision is not the member's")
		x.writeRange(m, tw, p, rangeReq{key: o.key})
		p.put(string(o.key), o.val, o.lease)
		check(tw.Put(o.key, []byte(o.val), lease.LeaseID(o.lease)) == p.rev, "a put's revision is not the next one")
		x.end(m, p, lead, tw.End)
	case opDelete:
		p := x.begin(m)
		tw := m.kv.Write(traceutil.TODO())
		x.checkHook(m, i)
		x.writeRange(m, tw, p, rangeReq{key: o.key, end: o.end})
		x.writeSub(m, tw, p, subOp{kind: 1, key: o.key, end: o.end})
		x.end(m, p, lead, tw.End)
	case opTxn:
		x.txn(m, o, lead, i)
	case opGrant:
		_, err := m.le.Grant(lease.LeaseID(o.id), 3600)
		check(err == nil, "a lease grant failed")
		x.checkHook(m, i)
		m.leases = append(m.leases, o.id)
		check(m.kv.Rev() == m.rev, "a lease grant made a revision")
	case opRevoke:
		p := x.begin(m)
		var ks []string
		for _, k := range x.keys {
			if e, ok := p.st[k]; ok && e.lease == o.id {
				ks = append(ks, k)
			}
		}
		for _, k := range ks {
			delete(p.st, k)
			p.changes = append(p.changes, change{del: true, key: k})
		}
		x.end(m, p, lead, func() {
			check(m.le.Revoke(lease.LeaseID(o.id)) == nil, "a lease revoke failed")
		})
		x.checkHook(m, i)
		var rest []int64
		for _, id := range m.leases {
			if id != o.id {
				rest = append(rest, id)
			}
		}
		m.leases = rest
		check(m.le.Lookup(lease.LeaseID(o.id)) == nil, "a revoked lease is still there")
	case opCompact:
		x.compact(m, o, lead)
	case opCommit:
		m.kv.Commit()
	case opRead:
		tr := m.kv.Read(mvcc.ConcurrentReadTxMode, traceutil.TODO())
		check(tr.Rev() == m.rev, "the writer's read is not at its revision")
		check(tr.FirstRev() == m.cmp, "the writer's read has the wrong compaction revision")
		res, err := tr.Range(context.TODO(), o.q.key, o.q.end, o.q.ro)
		checkRangeAt(x.keys, x.h.snapshot(), m.rev, m.cmp, o.q, res, err)
		tr.End()
	default:
		x.checkLeases(m)
	}
}

// begin returns the model of a write transaction on m, and raises m's revision bound.
func (x *runner) begin(m *member) *pending {
	st := x.h.snapshot()
	m.revHi.Store(m.rev + 1)
	return &pending{rev: m.rev + 1, st: copyState(st[m.rev])}
}

// end appends the pending revision to the history (the leader, if it changed anything), runs
// the store's End, checks the store's revision and publishes it.
func (x *runner) end(m *member, p *pending, lead bool, end func()) {
	if len(p.changes) > 0 && lead {
		check(len(x.h.snapshot()) == int(p.rev), "the leader's history is not at its revision")
		x.h.appendRev(p.st, p.changes)
		x.revisions.Add(1)
	}
	end()
	want := p.rev - 1
	if len(p.changes) > 0 {
		want = p.rev
	}
	m.rev = want
	check(m.kv.Rev() == want, "the store's revision is not the writer's")
	m.revLo.Store(want)
	m.revHi.Store(want)
}

// view returns the states as a read in the write transaction sees them (the pending revision
// appended once it has a change) and the revision it is at.
func (x *runner) view(p *pending) ([]map[string]kvRec, int64) {
	st := x.h.snapshot()
	if len(p.changes) == 0 {
		return st[:p.rev:p.rev], p.rev - 1
	}
	return append(st[:p.rev:p.rev], p.st), p.rev
}

func (x *runner) writeRange(m *member, tw mvcc.TxnWrite, p *pending, q rangeReq) {
	states, cur := x.view(p)
	res, err := tw.Range(context.TODO(), q.key, q.end, q.ro)
	checkRangeAt(x.keys, states, cur, m.cmp, q, res, err)
}

// writeSub runs one operation of a write transaction, checked.
func (x *runner) writeSub(m *member, tw mvcc.TxnWrite, p *pending, s subOp) {
	switch s.kind {
	case 0:
		p.put(string(s.key), s.val, s.lease)
		check(tw.Put(s.key, []byte(s.val), lease.LeaseID(s.lease)) == p.rev, "a put's revision is not the pending one")
	case 1:
		n := p.del(x.keys, s.key, s.end)
		gotN, rev := tw.DeleteRange(s.key, s.end)
		check(gotN == n, "a range delete deleted the wrong number of keys")
		if len(p.changes) > 0 {
			check(rev == p.rev, "a range delete's revision is not the pending one")
		} else {
			check(rev == p.rev-1, "a range delete in a transaction without changes has a revision")
		}
	default:
		x.writeRange(m, tw, p, s.q)
	}
}

// txn is the server's txn.Txn: with a write and the shared-buffer mode, the compare in a
// shared-buffer read transaction, ended, then a write transaction that must be at the read's
// revision; with a write otherwise, the compare in the write transaction; without, the compare
// in a concurrent read transaction made a read-only write transaction. Then the branch's
// operations.
func (x *runner) txn(m *member, o *op, lead bool, i int64) {
	cur := m.rev
	if !o.write {
		tr := m.kv.Read(mvcc.ConcurrentReadTxMode, traceutil.TODO())
		check(tr.Rev() == cur && tr.FirstRev() == m.cmp, "the writer's read transaction is not at its revision")
		states := x.h.snapshot()
		tw := mvcc.NewReadOnlyTxnWrite(tr)
		res, err := tw.Range(context.TODO(), o.q.key, o.q.end, o.q.ro)
		checkRangeAt(x.keys, states, cur, m.cmp, o.q, res, err)
		for _, s := range o.subs {
			res, err := tw.Range(context.TODO(), s.q.key, s.q.end, s.q.ro)
			checkRangeAt(x.keys, states, cur, m.cmp, s.q, res, err)
		}
		check(tw.Rev() == cur && len(tw.Changes()) == 0, "a read-only transaction changed something")
		tw.End()
		return
	}
	if o.shared {
		tr := m.kv.Read(mvcc.SharedBufReadTxMode, traceutil.TODO())
		check(tr.Rev() == cur && tr.FirstRev() == m.cmp, "the writer's read transaction is not at its revision")
		res, err := tr.Range(context.TODO(), o.q.key, o.q.end, o.q.ro)
		checkRangeAt(x.keys, x.h.snapshot(), cur, m.cmp, o.q, res, err)
		tr.End()
	}
	p := x.begin(m)
	tw := m.kv.Write(traceutil.TODO())
	x.checkHook(m, i)
	check(tw.Rev() == cur, "a write after a read of the only writer is not at the read's revision")
	if !o.shared {
		x.writeRange(m, tw, p, o.q)
	}
	for _, s := range o.subs {
		x.writeSub(m, tw, p, s)
	}
	check((len(tw.Changes()) > 0) == (len(p.changes) > 0), "a write transaction's changes are wrong")
	x.end(m, p, lead, tw.End)
}

// compact compacts m at o.rev: ErrCompacted at or below m's compaction revision (with a channel
// closed once the compactions before are done), ErrFutureRev past its revision; waits for the
// compaction if o.wait.
func (x *runner) compact(m *member, o *op, lead bool) {
	c := o.rev
	if c <= m.cmp {
		ch, err := m.kv.Compact(traceutil.TODO(), c)
		check(err == mvcc.ErrCompacted && ch != nil, "a compaction at a compacted revision did not fail")
		if o.wait {
			<-ch
		}
		return
	}
	if c > m.rev {
		ch, err := m.kv.Compact(traceutil.TODO(), c)
		check(err == mvcc.ErrFutureRev && ch == nil, "a compaction at a future revision did not fail")
		return
	}
	m.cmpHi.Store(c)
	ch, err := m.kv.Compact(traceutil.TODO(), c)
	check(err == nil && ch != nil, "a compaction failed")
	m.cmp = c
	m.cmpLo.Store(c)
	if lead {
		x.h.addComp(c)
		x.compactions.Add(1)
	}
	if o.wait {
		<-ch
	}
}

// checkHook checks that the post-lock hook ran with the index being applied.
func (x *runner) checkHook(m *member, i int64) {
	check(m.saved.Load() == i, "the post-lock hook did not run in the write's lock")
}

// ---------------------------------------------------------------------------------------------
// The readers

func inBounds(lo, v int64, hi *atomic.Int64, what string) {
	check(lo <= v, what+" is below its floor")
	check(v <= hi.Load(), what+" is above what was written")
}

// startReaders starts cfg.Readers readers on each member, each running up to cfg.Reads reads
// until stopReaders (between two restarts: a reader belongs to the members' current incarnations).
func (x *runner) startReaders() {
	x.readStop.Store(0)
	for _, m := range x.ms {
		for j := 0; j < x.cfg.Readers; j++ {
			x.readWg.Add(1)
			go func() {
				for n := 0; n < x.cfg.Reads && x.readStop.Load() == 0; n++ {
					x.readOne(m)
					x.reads.Add(1)
					time.Sleep(x.cfg.Mix.ReadPause)
				}
				x.readWg.Done()
			}()
		}
	}
}

// stopReaders stops the readers and waits for them.
func (x *runner) stopReaders() {
	x.readStop.Store(1)
	x.readWg.Wait()
}

func (x *runner) readOne(m *member) {
	lo, clo := m.revLo.Load(), m.cmpLo.Load()
	switch pick(x.cfg.Mix.Read, 6) {
	case 0:
		inBounds(lo, m.kv.Rev(), &m.revHi, "Rev")
	case 1:
		inBounds(clo, m.kv.FirstRev(), &m.cmpHi, "FirstRev")
	case 2:
		tr := m.kv.Read(mvcc.ConcurrentReadTxMode, traceutil.TODO())
		cur, cmp := tr.Rev(), tr.FirstRev()
		inBounds(lo, cur, &m.revHi, "a read transaction's revision")
		inBounds(clo, cmp, &m.cmpHi, "a read transaction's compaction revision")
		states := x.h.snapshot()
		nr := 1 + choose(3)
		for j := 0; j < nr; j++ {
			q := x.genRange(cur, cmp)
			res, err := tr.Range(context.TODO(), q.key, q.end, q.ro)
			checkRangeAt(x.keys, states, cur, cmp, q, res, err)
		}
		tr.End()
	case 3:
		tr := m.kv.Read(mvcc.ConcurrentReadTxMode, traceutil.TODO())
		cmp := tr.FirstRev()
		tw := mvcc.NewReadOnlyTxnWrite(tr)
		cur := tw.Rev()
		inBounds(lo, cur, &m.revHi, "a read-only transaction's revision")
		inBounds(clo, cmp, &m.cmpHi, "a read-only transaction's compaction revision")
		states := x.h.snapshot()
		q := x.genRange(cur, cmp)
		res, err := tw.Range(context.TODO(), q.key, q.end, q.ro)
		checkRangeAt(x.keys, states, cur, cmp, q, res, err)
		check(len(tw.Changes()) == 0, "a read-only transaction has changes")
		tw.End()
	case 4:
		q := x.genRange(m.revHi.Load(), clo)
		res, err := m.kv.Range(context.TODO(), q.key, q.end, q.ro)
		x.checkStoreRange(m, lo, clo, q, res, err)
	default:
		x.hashes()
	}
}

// checkStoreRange checks the store's own Range (its own read transaction: a revision in
// [lo, revHi], a compaction revision in [clo, cmpHi]).
func (x *runner) checkStoreRange(m *member, lo, clo int64, q rangeReq, res *mvcc.RangeResult, err error) {
	if err == mvcc.ErrCompacted {
		check(q.ro.Rev > 0 && q.ro.Rev < m.cmpHi.Load(), "a read of a revision not compacted failed with ErrCompacted")
		check(res != nil && len(res.KVs) == 0 && res.Count == -1 && res.Rev == 0,
			"a compacted revision's read returned a result")
		return
	}
	check(res != nil, "a read returned no result")
	inBounds(lo, res.Rev, &m.revHi, "a read's revision")
	checkRangeAt(x.keys, x.h.snapshot(), res.Rev, clo, q, res, err)
}

// hashes is the corruption checker: HashByRev of one revision on both members, each checked,
// and equal when they are of the same revision and compaction revision; and the members'
// compaction hashes, equal when of the same revisions.
func (x *runner) hashes() {
	r := int64(choose(int(x.ms[0].revHi.Load()) + 3))
	var hs []mvcc.KeyValueHash
	var errs []error
	for _, m := range x.ms {
		lo, clo := m.revLo.Load(), m.cmpLo.Load()
		h, cur, err := m.kv.HashStorage().HashByRev(r)
		x.checkHash(m, r, h, cur, err, lo, clo)
		hs = append(hs, h)
		errs = append(errs, err)
	}
	if errs[0] == nil && errs[1] == nil {
		x.sameHash(hs[0], hs[1])
	}
	for _, a := range x.ms[0].kv.HashStorage().Hashes() {
		for _, b := range x.ms[1].kv.HashStorage().Hashes() {
			x.sameHash(a, b)
		}
	}
	// the two members' compaction hashes against each other's HashByRev of their revision,
	// as etcd's CompactHashCheck compares them
	for j, m := range x.ms {
		other := x.ms[1-j]
		for _, a := range m.kv.HashStorage().Hashes() {
			b, _, err := other.kv.HashStorage().HashByRev(a.Revision)
			if err == nil {
				x.sameHash(a, b)
			}
		}
	}
}

// sameHash checks that two hashes of the same revision at the same compaction revision are
// equal, unless the state at that revision is empty (the restriction:
// issues/etcd-mvcc-compact-hash-empty-keyspace.md).
func (x *runner) sameHash(a, b mvcc.KeyValueHash) {
	if a.Revision != b.Revision || a.CompactRevision != b.CompactRevision {
		return
	}
	if len(x.h.snapshot()[a.Revision]) == 0 {
		return
	}
	check(a.Hash == b.Hash, "two members' hashes of the same revision and compaction revision differ")
	x.hashPairs.Add(1)
}

// checkHash checks HashByRev(r) on m: ErrFutureRev past the current revision, ErrCompacted
// below the compaction revision, else the hash of r (0: the current revision) at the compaction
// revision; or the hash a compaction at r stored, at the compaction revision before it.
func (x *runner) checkHash(m *member, r int64, h mvcc.KeyValueHash, cur int64, err error, lo, clo int64) {
	if err == mvcc.ErrFutureRev {
		check(r > 0 && r > cur, "a hash of a revision written failed with ErrFutureRev")
		inBounds(lo, cur, &m.revHi, "a hash's current revision")
		return
	}
	if err == mvcc.ErrCompacted {
		check(r > 0 && r < m.cmpHi.Load(), "a hash of a revision not compacted failed with ErrCompacted")
		return
	}
	check(err == nil, "a hash failed")
	if prev, ok := x.h.compPrev(r); ok && h.Revision == r && h.CompactRevision == prev {
		// the stored hash of the compaction at r (its current revision unchecked: the
		// restriction, issues/etcd-mvcc-hashbyrev-restore-rev1.md)
		return
	}
	inBounds(lo, cur, &m.revHi, "a hash's current revision")
	want := r
	if r == 0 {
		want = cur
	}
	check(h.Revision == want, "a hash is of the wrong revision")
	inBounds(clo, h.CompactRevision, &m.cmpHi, "a hash's compaction revision")
	check(r == 0 || r >= h.CompactRevision, "a hash of a compacted revision did not fail")
}

// ---------------------------------------------------------------------------------------------
// The watch streams

// A watcher's expectation: its range and filter (0 none, 1 no puts, 2 no deletes), its start
// revision, and the position of its next event (revision rev, the index-th matching change of
// it). A watcher from revision 0 starts somewhere in [floatLo, rev] until its first event
// anchors it (floatLo 0 once anchored, or for a watcher from a given revision). stamped says
// whether every response sent before it registered has been received (recvOne); cancelled
// whether it is being or was cancelled; compacted whether it received a compaction response.
type watcher struct {
	key, end  []byte
	filter    int
	start     int64
	floatLo   int64
	rev       int64
	index     int
	stamped   bool
	cancelled bool
	compacted bool
}

func (w *watcher) matches(ch change) bool {
	if !inRange(w.key, w.end, ch.key) {
		return false
	}
	if ch.del {
		return w.filter != 2
	}
	return w.filter != 1
}

// A stream is one watch stream of a member, with its watchers by id (in registration order in
// order), the largest revision of a response without events so far, and its goroutines' signals.
type stream struct {
	x         *runner
	m         *member
	kv        mvcc.WatchableKV
	ws        mvcc.WatchStream
	mu        sync.Mutex
	watchers  map[mvcc.WatchID]*watcher
	order     []mvcc.WatchID
	eventless int64
	stop      atomic.Int64
	regDone   sync.WaitGroup
	recvDone  sync.WaitGroup
}

// startEpoch opens m's watch streams, each with its receiving goroutine and its registering one,
// which acts until the writer stops it.
func (x *runner) startEpoch(m *member) {
	m.regs.Store(0)
	for j := 0; j < x.cfg.Streams; j++ {
		s := &stream{x: x, m: m, kv: m.kv, ws: m.kv.NewWatchStream(),
			watchers: map[mvcc.WatchID]*watcher{}}
		s.recvDone.Add(1)
		go func() {
			for s.recvOne() {
				time.Sleep(x.cfg.Mix.RecvPause)
			}
			s.recvDone.Done()
		}()
		s.regDone.Add(1)
		go func() {
			for s.stop.Load() == 0 {
				s.act()
				time.Sleep(x.cfg.Mix.Pause)
			}
			s.regDone.Done()
		}()
		m.streams = append(m.streams, s)
	}
}

// endEpoch stops registering on m's streams, waits until every watcher has every event up to m's
// revision (or was cancelled or compacted), and closes the streams.
func (x *runner) endEpoch(m *member) {
	for _, s := range m.streams {
		s.stop.Store(1)
	}
	for _, s := range m.streams {
		s.regDone.Wait()
	}
	for _, s := range m.streams {
		for !s.complete(m.rev) {
			time.Sleep(time.Millisecond)
		}
	}
	for _, s := range m.streams {
		s.ws.Close()
		s.recvDone.Wait()
		_, err := s.ws.Watch(context.TODO(), 0, x.genKey(), nil, 0)
		check(err == mvcc.ErrEmptyWatcherRange, "a watch on a closed stream did not fail")
		check(s.ws.Cancel(0) == mvcc.ErrWatcherNotExist, "a cancel on a closed stream did not fail")
	}
	m.streams = nil
}

// act is the registering goroutine's step: register a watcher, cancel one, ask for one's
// progress or the stream's, check the stream's revision, or watch an empty range (which must
// fail).
func (s *stream) act() {
	switch pick(s.x.cfg.Mix.Act, 6) {
	case 0:
		s.watch()
	case 1:
		s.cancel()
	case 2:
		s.mu.Lock()
		id, ok := s.pick()
		s.mu.Unlock()
		if ok {
			s.ws.RequestProgress(id)
		}
	case 3:
		s.ws.RequestProgressAll()
	case 4:
		lo := s.m.revLo.Load()
		inBounds(lo, s.ws.Rev(), &s.m.revHi, "a watch stream's revision")
	default:
		k := s.x.genKey()
		id, err := s.ws.Watch(context.TODO(), 0, k, k, 0)
		check(id == -1 && err == mvcc.ErrEmptyWatcherRange, "a watch of an empty range did not fail")
	}
}

// pick returns a watcher not cancelled, if any (s.mu held).
func (s *stream) pick() (mvcc.WatchID, bool) {
	var live []mvcc.WatchID
	for _, id := range s.order {
		if !s.watchers[id].cancelled {
			live = append(live, id)
		}
	}
	if len(live) == 0 {
		return 0, false
	}
	return live[choose(len(live))], true
}

// watch registers a watcher (the stream picks its id, as etcd's client asks): from revision 0
// or any revision up to two past the member's, over any non-empty range, with any filter.
func (s *stream) watch() {
	if s.m.regs.Load() >= int64(s.x.cfg.Watchers) {
		return
	}
	s.m.regs.Add(1)
	x := s.x
	w := &watcher{key: x.genKey(), end: x.genEnd(), filter: choose(3)}
	if len(w.end) > 0 && string(w.end) <= string(w.key) {
		w.end = nil
	}
	switch pick(x.cfg.Mix.Start, 3) {
	case 1:
		w.start = 1 + int64(choose(int(s.m.revHi.Load())+2))
	case 2:
		w.start = s.m.cmpLo.Load()
		if w.start < 1 {
			w.start = 1
		}
	}
	var fcs []mvcc.FilterFunc
	if w.filter == 1 {
		fcs = append(fcs, func(e *mvccpb.Event) bool { return e.Type == mvccpb.Event_PUT })
	} else if w.filter == 2 {
		fcs = append(fcs, func(e *mvccpb.Event) bool { return e.Type == mvccpb.Event_DELETE })
	}
	s.mu.Lock()
	lo := s.m.revLo.Load()
	id, err := s.ws.Watch(context.TODO(), 0, w.key, w.end, w.start, fcs...)
	hi := s.m.revHi.Load()
	check(err == nil, "a watch failed")
	check(s.watchers[id] == nil, "a watch id was reused")
	if w.start == 0 {
		w.floatLo, w.rev = lo+1, hi+1
	} else {
		w.rev = w.start
	}
	s.watchers[id] = w
	s.order = append(s.order, id)
	s.mu.Unlock()
}

// cancel cancels a watcher not cancelled (marked first, so that the receiver stops counting on
// the stream's progress responses for it), and cancels it again, which may fail.
func (s *stream) cancel() {
	s.mu.Lock()
	id, ok := s.pick()
	if ok {
		s.watchers[id].cancelled = true
	}
	s.mu.Unlock()
	if !ok {
		return
	}
	check(s.ws.Cancel(id) == nil, "a cancel failed")
	err := s.ws.Cancel(id)
	check(err == nil || err == mvcc.ErrWatcherNotExist, "a second cancel failed otherwise")
	s.x.cancels.Add(1)
}

// expect returns w's next expected change at or after its position, up to revision upto (false if
// there is none).
func (s *stream) expect(w *watcher, upto int64) (change, int64, bool) {
	for r := w.rev; r <= upto; r++ {
		seen := 0
		for _, ch := range s.x.h.changesAt(r) {
			if !w.matches(ch) {
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

// covered checks that w has received every change up to P.
func (s *stream) covered(w *watcher, p int64, what string) {
	_, _, more := s.expect(w, p)
	check(!more, what+" came before a change at or below its revision")
}

// recvOne receives one response and checks it (false once the channel is closed and drained).
// Before it blocks, it polls the channel with the stream's lock held: if it is empty, every
// response sent so far has been received, so every watcher registered so far is stamped (v3rpc's
// sendLoop drains its channel down to a new watcher's stamp the same way): a stream progress
// response received later was sent after the watcher registered, and covers it.
func (s *stream) recvOne() bool {
	s.mu.Lock()
	select {
	case resp, ok := <-s.ws.Chan():
		if !ok {
			s.mu.Unlock()
			return false
		}
		s.receive(resp)
		s.mu.Unlock()
		return true
	default:
		for _, id := range s.order {
			s.watchers[id].stamped = true
		}
		s.mu.Unlock()
	}
	resp, ok := <-s.ws.Chan()
	if !ok {
		return false
	}
	s.mu.Lock()
	s.receive(resp)
	s.mu.Unlock()
	return true
}

// receive checks a response of the stream (s.mu held).
func (s *stream) receive(resp mvcc.WatchResponse) {
	m := s.m
	check(resp.Revision <= m.revHi.Load(), "a watch response is at a revision not yet written")
	if len(resp.Events) == 0 && resp.CompactRevision == 0 {
		// progress (the watcher's, or the stream's): the revisions of the responses without events
		// never decrease
		check(resp.Revision >= s.eventless, "a progress response's revision went back")
		s.eventless = resp.Revision
		s.x.progress.Add(1)
	}
	if resp.WatchID == -1 {
		// the stream's progress: covers every watcher stamped before it and not cancelled
		check(len(resp.Events) == 0 && resp.CompactRevision == 0 && resp.Revision >= 1,
			"a stream's progress response is not progress")
		for _, id := range s.order {
			w := s.watchers[id]
			if w.stamped && !w.cancelled {
				s.covered(w, resp.Revision, "a stream's progress response")
			}
		}
		return
	}
	w := s.watchers[resp.WatchID]
	check(w != nil, "a watch response for an unknown watcher")
	if resp.CompactRevision != 0 {
		check(len(resp.Events) == 0 && resp.Revision == 0, "a compaction response has events")
		check(0 < resp.CompactRevision && resp.CompactRevision <= m.cmpHi.Load(),
			"a watcher was compacted at a revision not compacted")
		w.compacted = true
		s.x.compacted.Add(1)
		return
	}
	if len(resp.Events) == 0 {
		// the watcher's progress: at least its first revision less one, after its every change up
		// to its revision
		lower := w.start
		if w.floatLo > lower {
			lower = w.floatLo
		}
		check(resp.Revision+1 >= lower, "a progress response is below its watcher's start")
		s.covered(w, resp.Revision, "a progress response")
		return
	}
	for _, ev := range resp.Events {
		r := ev.Kv.ModRevision
		check(r <= resp.Revision, "a watch response's revision is below its event's")
		if w.floatLo > 0 {
			check(r >= w.floatLo, "a watcher from now received an event from before it")
			if r < w.rev {
				w.rev, w.index = r, 0
			}
			w.floatLo = 0
		}
		want, wr, ok := s.expect(w, r)
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
		if w.rev < r {
			w.rev, w.index = r, 0
		}
		w.index++
		s.x.events.Add(1)
		if choose(4) == 0 {
			// the watch server's previous key-value: the key at the revision before the event
			clo := m.cmpLo.Load()
			lo := m.revLo.Load()
			q := rangeReq{key: ev.Kv.Key, ro: mvcc.RangeOptions{Rev: r - 1}}
			res, err := s.kv.Range(context.TODO(), q.key, q.end, q.ro)
			s.x.checkStoreRange(m, lo, clo, q, res, err)
		}
	}
}

// complete says whether every watcher not cancelled or compacted has every change up to upto.
func (s *stream) complete(upto int64) bool {
	s.mu.Lock()
	defer s.mu.Unlock()
	for _, id := range s.order {
		w := s.watchers[id]
		if w.cancelled || w.compacted {
			continue
		}
		if _, _, more := s.expect(w, upto); more {
			return false
		}
	}
	return true
}

// ---------------------------------------------------------------------------------------------
// The run

// write is the writer: the log's operations on the leader, the follower catching up, snapshots
// installed on the follower, restarts; then the follower caught up.
func (x *runner) write() {
	l, f := x.ms[0], x.ms[1]
	for l.ops < x.cfg.Ops {
		switch pick(x.cfg.Mix.Step, 6) {
		case 0:
			o := x.gen(l)
			x.log = append(x.log, o)
			x.apply(l, o, true)
		case 1:
			if f.ops < l.ops {
				x.apply(f, x.log[f.ops], false)
			}
		case 2:
			if f.ops < l.ops {
				x.restore(l, f)
			}
		case 3:
			x.restart(l)
		case 4:
			x.restart(f)
		default:
			x.checkLeases(l)
			x.checkLeases(f)
		}
	}
	for f.ops < l.ops {
		x.apply(f, x.log[f.ops], false)
	}
}

// checkAll reads every revision of m not compacted, in full.
func (x *runner) checkAll(m *member) {
	states := x.h.snapshot()
	from := m.cmp
	if from < 1 {
		from = 1
	}
	tr := m.kv.Read(mvcc.ConcurrentReadTxMode, traceutil.TODO())
	for r := from; r <= m.rev; r++ {
		q := rangeReq{key: []byte{0}, end: []byte{}, ro: mvcc.RangeOptions{Rev: r}}
		res, err := tr.Range(context.TODO(), q.key, q.end, q.ro)
		checkRangeAt(x.keys, states, m.rev, m.cmp, q, res, err)
	}
	if m.cmp > 1 {
		q := rangeReq{key: []byte{0}, end: []byte{}, ro: mvcc.RangeOptions{Rev: m.cmp - 1}}
		res, err := tr.Range(context.TODO(), q.key, q.end, q.ro)
		checkRangeAt(x.keys, states, m.rev, m.cmp, q, res, err)
	}
	tr.End()
}

// Run runs the tester; it panics if a check fails.
func Run(cfg Config) Report {
	cfg = normalize(cfg)
	x := &runner{cfg: cfg, keys: walkKeys(nil, "", cfg.Depth), lg: zap.NewNop(),
		h: &history{states: []map[string]kvRec{{}, {}}, changes: [][]change{nil, nil}}}
	x.ms = append(x.ms, x.newMember(0, memberPath(cfg.Prefix, 0)))
	x.ms = append(x.ms, x.newMember(1, memberPath(cfg.Prefix, 1)))
	for _, m := range x.ms {
		x.startEpoch(m)
	}
	x.startReaders()
	x.write()
	x.stopReaders()
	if hashing(x.cfg.Mix.Read) {
		x.hashes()
	}
	for _, m := range x.ms {
		x.endEpoch(m)
		x.shut(m)
		x.open(m)
		x.checkAll(m)
		x.shut(m)
	}
	return Report{Revisions: x.revisions.Load(), Events: x.events.Load(), Progress: x.progress.Load(),
		Compacted: x.compacted.Load(), Cancels: x.cancels.Load(), Reads: x.reads.Load(),
		HashPairs: x.hashPairs.Load(), Compactions: x.compactions.Load(),
		Restores: x.restores.Load(), Restarts: x.restarts.Load()}
}

// Main runs the tester with MainConfig (config.go), the members' files mvccfull-0-0.db,
// mvccfull-1-0.db, ... in the current directory (which must not exist).
func Main() {
	Run(MainConfig("mvccfull"))
}
