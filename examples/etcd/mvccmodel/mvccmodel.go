// Package mvccmodel is a randomized test of etcd's mvcc store (go.etcd.io/etcd/server/v3/storage/mvcc)
// against a reference model, meant to pin down mvcc's observable behavior well enough that a
// reimplementation of it (other index or storage structures) can be checked against it.
//
// Random operations run concurrently, covering mvcc's public API:
//
//   - one applier goroutine makes every change, as etcd's apply loop does (mvcc supports one
//     writer; see "Restrictions"): write transactions (Put, DeleteRange, Range, Rev, FirstRev,
//     Changes), the store's own Put and DeleteRange, Compact, Commit, Restore, HashStorage().Hash,
//     lease grants and revokes (a revoke deletes the lease's keys through mvcc, in one revision),
//     puts with a lease, checks of the lessor's view of the keys' leases, and reads;
//   - reader goroutines: read transactions in both modes (some wrapped by NewReadOnlyTxnWrite),
//     the store's own Range, Rev and FirstRev, HashStorage().HashByRev and Hashes;
//   - watch-stream goroutines, each owning a stream (and a goroutine receiving from its Chan):
//     Watch (auto or explicit IDs, duplicate IDs, empty ranges, any start revision, filters),
//     Cancel, RequestProgress, RequestProgressAll, Rev and Close (then a new stream).
//
// After the run, the store is checked quiescent (every revision read and hashed), then closed and
// reopened over the same backend (a restart) and checked again.
//
// How it checks. Every call is stamped with a logical clock before it starts and after it returns.
// The applier's log, replayed in order, builds the model: the key-values at each revision, the
// changes of each revision, the compactions; each of its operations is checked as it is replayed.
// Each replayed operation that changes what a reader can see (the store's revision, its compaction
// revision) starts an epoch. Every other observation must agree with the model at some epoch that
// may have been current during its call: one that began before the call returned and was not
// replaced before the call started. Watch responses are checked against the model's changes, per
// watcher, in the order the stream delivered them, and at the end every live watcher must have
// received every change it watches.
//
// The model is in this file, beside the calls it checks: model, txn, checkRange, hash.
//
// Restrictions (each an execution etcd does not produce, or a recorded finding; see
// notes/mvccmodel.md):
//   - one goroutine makes every change (writes, Compact, Commit, Restore, lease revokes); with
//     concurrent writers a progress request can deadlock
//     (nonissues/etcd-mvcc-progress-lock-order-deadlock.md); Hash, documented as not to be used
//     with ongoing transactions, runs on that goroutine too;
//   - a revision changes each key at most once (etcd's gRPC layer rejects a txn that changes a key
//     twice; nonissues/etcd-mvcc-watch-compact-rev-subrev-lost.md);
//   - no Compact(0) (issues/etcd-mvcc-hashbyrev-zero-stored.md,
//     nonissues/etcd-restore-scheduled-compact-zero.md), no negative revisions (etcd's gRPC layer
//     rejects them; nonissues/etcd-mvcc-watch-negative-start-rev.md);
//   - a canceled watch ID is never reused on its stream (its queued responses cannot be told
//     apart from the new watch's: issues/etcd-watch-id-reuse-stale-events.md);
//   - HashStorage().Store is not called (only mvcc's compaction calls it);
//   - a compaction's done channel is required to close only if no Restore came after it
//     (issues/etcd-restore-pending-compaction-unclosed.md);
//   - Hash's value is not checked (it hashes the whole backend: lease and meta buckets, and
//     revisions a compaction in progress has not yet deleted), only its revision.
package mvccmodel

import (
	"bytes"
	"context"
	"errors"
	"fmt"
	"hash/crc32"
	"math/rand/v2"
	"slices"
	"sort"
	"strconv"
	"sync"
	"sync/atomic"
	"time"

	"go.uber.org/zap"
	"google.golang.org/protobuf/proto"

	"go.etcd.io/etcd/api/v3/mvccpb"
	"go.etcd.io/etcd/pkg/v3/traceutil"
	"go.etcd.io/etcd/server/v3/lease"
	"go.etcd.io/etcd/server/v3/storage/backend"
	"go.etcd.io/etcd/server/v3/storage/mvcc"
	"go.etcd.io/etcd/server/v3/storage/schema"
)

// A Config is a run's: the backend's file (it must not exist), the seed, the number of the
// applier's operations (the readers and watch streams run until it is done), the number of
// readers and of watch streams, and how long to wait at the end for every watcher to receive every
// change and every compaction to finish.
type Config struct {
	Path       string
	Seed       uint64
	ApplierOps int
	Readers    int
	Streams    int
	Drain      time.Duration
}

// ---------------------------------------------------------------------------------------------
// Keys and random requests.

const letters = "abcde"

// genKey returns a random key: one to three letters (155 keys, enough for the index's B-tree to
// split; some are prefixes of others).
func genKey(r *rand.Rand) []byte {
	k := make([]byte, 1+r.IntN(3))
	for i := range k {
		k[i] = letters[r.IntN(len(letters))]
	}
	return k
}

// allKeys is every key genKey returns, in byte order.
var allKeys = func() []string {
	var ks []string
	var gen func(prefix string)
	gen = func(prefix string) {
		for _, c := range letters {
			k := prefix + string(c)
			ks = append(ks, k)
			if len(k) < 3 {
				gen(k)
			}
		}
	}
	gen("")
	sort.Strings(ks)
	return ks
}()

// genEnd returns a range end: nil (the key alone), empty (every key from the key on) or a key
// (which may be at or below the key: an empty range).
func genEnd(r *rand.Rand) []byte {
	switch r.IntN(4) {
	case 0:
		return nil
	case 1:
		return []byte{}
	default:
		return genKey(r)
	}
}

// inRange says whether k is in the range of key and end (as genEnd's).
func inRange(key, end []byte, k string) bool {
	if end == nil {
		return k == string(key)
	}
	return k >= string(key) && (len(end) == 0 || k < string(end))
}

// genRev returns a revision for a request made around revision hint: anything from 0 to one past
// it (0 meaning the current revision where the API says so).
func genRev(r *rand.Rand, hint int64) int64 { return r.Int64N(hint + 2) }

type rangeReq struct {
	key, end []byte
	ro       mvcc.RangeOptions
}

func genRange(r *rand.Rand, hint int64) rangeReq {
	q := rangeReq{key: genKey(r), end: genEnd(r)}
	q.ro.Rev = genRev(r, hint)
	if r.IntN(4) == 0 {
		q.ro.Rev = -1
	}
	q.ro.Limit = int64(r.IntN(5)) - 1
	q.ro.CountOnly = r.IntN(5) == 0
	q.ro.FastKeysOnly = r.IntN(4) == 0
	q.ro.WithTotalCount = r.IntN(2) == 0
	return q
}

// ---------------------------------------------------------------------------------------------
// The model.

// A kvRec is a key's value in the model, with the revision (main, sub) of its last change.
type kvRec struct {
	val         string
	create, ver int64
	mod, sub    int64
	lease       int64
}

// A change is one change of a revision: a put of kv, or a delete of key.
type change struct {
	key string
	del bool
	kv  kvRec
}

type compaction struct{ rev, prev int64 }

// A model is the store's history: states[r] the key-values at revision r and changes[r] the
// changes that made revision r (revision 1, the first, is empty), and the compactions that
// succeeded, in order.
type model struct {
	states      []map[string]kvRec
	changes     [][]change
	compact     int64
	compactions []compaction
	// memoized hashes (the checks run after the model is complete)
	hashes map[[2]int64]mvcc.KeyValueHash
	stored []mvcc.KeyValueHash
}

func newModel() *model {
	return &model{states: []map[string]kvRec{{}, {}}, changes: [][]change{nil, nil}, compact: -1,
		hashes: map[[2]int64]mvcc.KeyValueHash{}}
}

func (m *model) rev() int64 { return int64(len(m.states) - 1) }

// A point is what a reader can see of the store's state: its revision, its compaction revision
// (-1 before any), and how many compactions have succeeded; restoring marks a Restore in progress.
type point struct {
	rev, compact int64
	ncompact     int
	restoring    bool
}

func (m *model) point() point {
	return point{rev: m.rev(), compact: m.compact, ncompact: len(m.compactions)}
}

// A txn is a write transaction in progress over the model: the state with its changes so far.
type txn struct {
	m       *model
	st      map[string]kvRec
	changes []change
}

func (m *model) begin() *txn {
	st := make(map[string]kvRec, len(m.states[m.rev()]))
	for k, v := range m.states[m.rev()] {
		st[k] = v
	}
	return &txn{m: m, st: st}
}

// next is the revision the transaction writes; cur the one its reads see (next once it has
// changed something).
func (t *txn) next() int64 { return t.m.rev() + 1 }
func (t *txn) cur() int64 {
	if len(t.changes) > 0 {
		return t.next()
	}
	return t.m.rev()
}

// stateAt is the state a read in the transaction sees at revision r.
func (t *txn) stateAt(r int64) map[string]kvRec {
	if r == t.next() {
		return t.st
	}
	return t.m.states[r]
}

func (t *txn) put(k, v string, l int64) {
	rec := kvRec{val: v, create: t.next(), ver: 1, mod: t.next(), sub: int64(len(t.changes)), lease: l}
	if e, ok := t.st[k]; ok {
		rec.create, rec.ver = e.create, e.ver+1
	}
	t.st[k] = rec
	t.changes = append(t.changes, change{key: k, kv: rec})
}

// del deletes the live keys of the range, in key order, and returns how many.
func (t *txn) del(key, end []byte) int64 {
	var n int64
	for _, k := range allKeys {
		if _, ok := t.st[k]; ok && inRange(key, end, k) {
			delete(t.st, k)
			t.changes = append(t.changes, change{key: k, del: true})
			n++
		}
	}
	return n
}

func (t *txn) commit() {
	if len(t.changes) > 0 {
		t.m.states = append(t.m.states, t.st)
		t.m.changes = append(t.m.changes, t.changes)
	}
}

// checkRange checks a range read's result at revision cur, under compaction revision compact,
// reading the state at a revision with stateAt.
func checkRange(stateAt func(int64) map[string]kvRec, cur, compact int64, q rangeReq, res *mvcc.RangeResult, err error) error {
	if q.ro.Rev > cur {
		if err != mvcc.ErrFutureRev || res == nil || len(res.KVs) != 0 || res.Count != -1 || res.Rev != cur {
			return fmt.Errorf("range %+v at %d: want ErrFutureRev, got %v %v", q, cur, res, err)
		}
		return nil
	}
	rev := q.ro.Rev
	if rev <= 0 {
		rev = cur
	}
	if rev < compact {
		if err != mvcc.ErrCompacted || res == nil || len(res.KVs) != 0 || res.Count != -1 || res.Rev != 0 {
			return fmt.Errorf("range %+v at %d compacted at %d: want ErrCompacted, got %v %v", q, cur, compact, res, err)
		}
		return nil
	}
	if err != nil || res == nil || res.Rev != cur {
		return fmt.Errorf("range %+v at %d: got %v %v", q, cur, res, err)
	}
	st := stateAt(rev)
	var match []string
	for _, k := range allKeys {
		if _, ok := st[k]; ok && inRange(q.key, q.end, k) {
			match = append(match, k)
		}
	}
	n := len(match)
	if q.ro.CountOnly {
		if len(res.KVs) != 0 || res.Count != n {
			return fmt.Errorf("count-only range %+v at %d: want %d, got %d (%d kvs)", q, rev, n, res.Count, len(res.KVs))
		}
		return nil
	}
	taken := n
	if q.ro.Limit > 0 && int(q.ro.Limit) < n {
		taken = int(q.ro.Limit)
	}
	count := n
	if q.end != nil && q.ro.Limit > 0 && !q.ro.WithTotalCount {
		count = taken
	}
	if res.Count != count || len(res.KVs) != taken {
		return fmt.Errorf("range %+v at %d: want count %d and %d kvs, got %d and %d", q, rev, count, taken, res.Count, len(res.KVs))
	}
	for i := range taken {
		if err := checkKV(res.KVs[i], match[i], st[match[i]], q.ro.FastKeysOnly); err != nil {
			return fmt.Errorf("range %+v at %d: %v", q, rev, err)
		}
	}
	return nil
}

func checkKV(kv *mvccpb.KeyValue, k string, e kvRec, keysOnly bool) error {
	want := &mvccpb.KeyValue{Key: []byte(k), CreateRevision: e.create, ModRevision: e.mod, Version: e.ver}
	if !keysOnly {
		want.Value, want.Lease = []byte(e.val), e.lease
	}
	if !proto.Equal(kv, want) {
		return fmt.Errorf("want key-value %v, got %v", want, kv)
	}
	return nil
}

// ---------------------------------------------------------------------------------------------
// Hashes.

// keepSet is the revision of the last change of each key live at revision r: what a compaction
// at r keeps of the revisions up to r, but its tombstones.
func (m *model) keepSet(r int64) map[mvcc.Revision]bool {
	keep := map[mvcc.Revision]bool{}
	if r >= 1 {
		for _, e := range m.states[r] {
			keep[mvcc.Revision{Main: e.mod, Sub: e.sub}] = true
		}
	}
	return keep
}

// deletedAt says whether revision r deletes a key it leaves deleted (a compaction at r keeps
// that tombstone).
func (m *model) deletedAt(r int64) bool {
	for _, c := range m.changes[r] {
		if _, live := m.states[r][c.key]; c.del && !live {
			return true
		}
	}
	return false
}

// hash is mvcc's hash of the key bucket for compaction revision c and revision r (kvHasher): every
// revision up to r, with those up to c only if keep has them -- or, when keep is empty, if they
// are still in the backend (stored) -- and without a tombstone at exactly c. Each revision is
// hashed as the backend stores it: its bucket key, then the marshaled key-value.
func (m *model) hash(c, r int64, keep map[mvcc.Revision]bool, keepNonEmpty bool, stored map[mvcc.Revision]bool) uint32 {
	h := crc32.New(crc32.MakeTable(crc32.Castagnoli))
	h.Write(schema.Key.Name())
	for main := int64(1); main <= r; main++ {
		for sub, ch := range m.changes[main] {
			rev := mvcc.Revision{Main: main, Sub: int64(sub)}
			if main <= c && (keepNonEmpty && !keep[rev] || !keepNonEmpty && !stored[rev]) {
				continue
			}
			if main == c && ch.del {
				continue
			}
			key := mvcc.RevToBytes(rev, mvcc.NewRevBytes())
			kv := &mvccpb.KeyValue{Key: []byte(ch.key)}
			if ch.del {
				key = append(key, 't')
			} else {
				kv = &mvccpb.KeyValue{Key: []byte(ch.key), Value: []byte(ch.kv.val), CreateRevision: ch.kv.create,
					ModRevision: ch.kv.mod, Version: ch.kv.ver, Lease: ch.kv.lease}
			}
			v, err := proto.Marshal(kv)
			if err != nil {
				panic(err)
			}
			h.Write(key)
			h.Write(v)
		}
	}
	return h.Sum32()
}

// hashByRev is HashByRev(r)'s hash under compaction revision c. It is known only if a key is live
// at r: with none, keep is empty and the hash covers the revisions up to c still in the backend,
// which depends on how far the compaction at c has got (notes/mvccmodel.md, "HashByRev of an empty
// key space"); then only the revisions are checked.
func (m *model) hashByRev(c, r int64) (h mvcc.KeyValueHash, known bool) {
	if len(m.states[r]) == 0 {
		return mvcc.KeyValueHash{CompactRevision: c, Revision: r}, false
	}
	if h, ok := m.hashes[[2]int64{c, r}]; ok {
		return h, true
	}
	h = mvcc.KeyValueHash{Hash: m.hash(c, r, m.keepSet(r), true, nil), CompactRevision: c, Revision: r}
	m.hashes[[2]int64{c, r}] = h
	return h, true
}

// storedHash is the hash the i-th compaction stores, if the one before it had finished: of the
// revisions after the previous compaction up to it (those up to the previous one still in the
// backend are what it kept: keepSet(c.prev) and tombstones, which are not hashed).
func (m *model) storedHash(i int) mvcc.KeyValueHash {
	for len(m.stored) <= i {
		c := m.compactions[len(m.stored)]
		keep := m.keepSet(c.rev)
		m.stored = append(m.stored, mvcc.KeyValueHash{
			Hash:            m.hash(c.prev, c.rev, keep, len(keep) > 0 || m.deletedAt(c.rev), m.keepSet(c.prev)),
			CompactRevision: c.prev, Revision: c.rev})
	}
	return m.stored[i]
}

func (m *model) checkHashByRev(p point, q int64, h mvcc.KeyValueHash, cur int64, err error) error {
	// A stored hash, returned with the store's revision -- which during a Restore is 1
	// (issues/etcd-mvcc-hashbyrev-restore-rev1.md): accepted then.
	if err == nil && h.Revision == q && (cur == p.rev || p.restoring && cur == 1) {
		for i := range p.ncompact {
			if m.storedHash(i) == h {
				return nil
			}
		}
	}
	var want mvcc.KeyValueHash
	var wantCur int64
	var wantErr error
	switch {
	case q > 0 && q < p.compact:
		wantErr = mvcc.ErrCompacted
	case q > p.rev:
		wantCur, wantErr = p.rev, mvcc.ErrFutureRev
	default:
		r := q
		if r == 0 {
			r = p.rev
		}
		var known bool
		want, known = m.hashByRev(p.compact, r)
		wantCur = p.rev
		if !known {
			want.Hash = h.Hash
		}
	}
	if h != want || cur != wantCur || err != wantErr {
		return fmt.Errorf("HashByRev(%d) at %+v: want %+v %d %v, got %+v %d %v", q, p, want, wantCur, wantErr, h, cur, err)
	}
	return nil
}

func (m *model) checkHashes(p point, hs []mvcc.KeyValueHash) error {
	if len(hs) > 10 {
		return fmt.Errorf("Hashes: %d hashes, more than 10", len(hs))
	}
	for j, h := range hs {
		if j > 0 && hs[j-1].Revision >= h.Revision {
			return fmt.Errorf("Hashes: not in increasing revision order: %+v", hs)
		}
		ok := false
		for i := range p.ncompact {
			ok = ok || m.storedHash(i) == h
		}
		if !ok {
			return fmt.Errorf("Hashes at %+v: %+v is no compaction's hash", p, h)
		}
	}
	return nil
}

// ---------------------------------------------------------------------------------------------
// Recording.

// A clock stamps calls: before a call starts and after it returns.
type clock struct{ n atomic.Int64 }

func (c *clock) now() int64 { return c.n.Add(1) }

// An obs is an observation made between times a and b, checked against a point of the model.
type obs struct {
	what string
	a, b int64
	ok   func(m *model, p point) error
}

// A step is one of the applier's operations, between times a and b, replayed on the model.
type step struct {
	what    string
	a, b    int64
	apply   func(m *model) error
	restore bool
}

// An epoch is a point of the model and the times of the step that made it.
type epoch struct {
	p    point
	a, b int64
}

// ---------------------------------------------------------------------------------------------
// The applier.

type applier struct {
	kv     mvcc.WatchableKV
	be     backend.Backend
	le     lease.Lessor
	r      *rand.Rand
	clk    *clock
	steps  []step
	obs    []obs
	leases []int64 // live leases
	nextID int64
	vals   int
	// compactions' done channels, with the number of Restores before each
	chans    []compactChan
	restores int
}

type compactChan struct {
	ch       <-chan struct{}
	restores int
	what     string
}

func (ap *applier) step(what string, a int64, apply func(m *model) error) {
	ap.steps = append(ap.steps, step{what: what, a: a, b: ap.clk.now(), apply: apply})
}

func (ap *applier) observe(what string, a int64, ok func(m *model, p point) error) {
	ap.obs = append(ap.obs, obs{what, a, ap.clk.now(), ok})
}

func (ap *applier) val() string {
	ap.vals++
	if ap.r.IntN(10) == 0 {
		return ""
	}
	return "v" + strconv.Itoa(ap.vals)
}

// genLease returns no lease half the time, else a live lease, if any.
func (ap *applier) genLease() int64 {
	if ap.r.IntN(2) == 0 || len(ap.leases) == 0 {
		return 0
	}
	return ap.leases[ap.r.IntN(len(ap.leases))]
}

// hint returns the store's revision, for generating requests (checked like any read).
func (ap *applier) hint() int64 {
	a := ap.clk.now()
	rev := ap.kv.Rev()
	ap.observe("Rev", a, func(m *model, p point) error { return expect(rev == p.rev, "Rev %d at %+v", rev, p) })
	return rev
}

func (ap *applier) run(n int) {
	for range n {
		switch ap.r.IntN(13) {
		case 0, 1, 2:
			ap.writeTxn()
		case 3:
			ap.put()
		case 4:
			ap.deleteRange()
		case 5:
			ap.compact()
		case 6:
			ap.kv.Commit()
		case 7:
			ap.restore()
		case 8:
			ap.hash()
		case 9:
			ap.grant()
		case 10:
			ap.revoke()
		case 11:
			ap.checkLeases()
		default:
			ap.obs = append(ap.obs, readTxn(ap.kv, ap.r, ap.clk, ap.hint()))
		}
	}
}

// writeTxn runs a write transaction of up to four random operations; no key is changed twice
// (as etcd's gRPC layer requires).
func (ap *applier) writeTxn() {
	hint := ap.hint()
	a := ap.clk.now()
	tw := ap.kv.Write(traceutil.TODO())
	base, first := tw.Rev(), tw.FirstRev()
	changed := map[string]bool{}
	var ops []func(t *txn) error
	for range ap.r.IntN(5) {
		switch ap.r.IntN(3) {
		case 0:
			k := genKey(ap.r)
			if changed[string(k)] {
				continue
			}
			changed[string(k)] = true
			v, l := ap.val(), ap.genLease()
			rev := tw.Put(k, []byte(v), lease.LeaseID(l))
			ops = append(ops, func(t *txn) error {
				t.put(string(k), v, l)
				return expect(rev == t.next(), "Put returned %d, want %d", rev, t.next())
			})
		case 1:
			key, end := genKey(ap.r), genEnd(ap.r)
			if slices.ContainsFunc(allKeys, func(k string) bool { return changed[k] && inRange(key, end, k) }) {
				continue
			}
			for _, k := range allKeys {
				if inRange(key, end, k) {
					changed[k] = true
				}
			}
			n, rev := tw.DeleteRange(key, end)
			ops = append(ops, func(t *txn) error {
				want := t.del(key, end)
				return expect(n == want && rev == t.cur(), "DeleteRange(%q, %q) returned %d %d, want %d %d", key, end, n, rev, want, t.cur())
			})
		default:
			q := genRange(ap.r, hint)
			res, err := tw.Range(context.TODO(), q.key, q.end, q.ro)
			ops = append(ops, func(t *txn) error { return checkRange(t.stateAt, t.cur(), t.m.compact, q, res, err) })
		}
	}
	var changes []*mvccpb.KeyValue
	for _, c := range tw.Changes() {
		changes = append(changes, proto.Clone(c).(*mvccpb.KeyValue))
	}
	tw.End()
	ap.step("write txn", a, func(m *model) error {
		// a write transaction's FirstRev is 0, not the documented compaction revision
		// (nonissues/etcd-mvcc-txnwrite-firstrev-zero.md): either is accepted
		if base != m.rev() || first != m.compact && first != 0 {
			return fmt.Errorf("write txn opened at Rev %d FirstRev %d, want %d %d", base, first, m.rev(), m.compact)
		}
		t := m.begin()
		for _, op := range ops {
			if err := op(t); err != nil {
				return err
			}
		}
		if err := checkChanges(t, changes); err != nil {
			return err
		}
		t.commit()
		return nil
	})
}

// checkChanges checks a write transaction's Changes: a put's new key-value, a delete's key alone.
func checkChanges(t *txn, got []*mvccpb.KeyValue) error {
	if len(got) != len(t.changes) {
		return fmt.Errorf("Changes: %d, want %d", len(got), len(t.changes))
	}
	for i, c := range t.changes {
		want := &mvccpb.KeyValue{Key: []byte(c.key)}
		if !c.del {
			want = &mvccpb.KeyValue{Key: []byte(c.key), Value: []byte(c.kv.val), CreateRevision: c.kv.create,
				ModRevision: c.kv.mod, Version: c.kv.ver, Lease: c.kv.lease}
		}
		if !proto.Equal(got[i], want) {
			return fmt.Errorf("Changes[%d]: %v, want %v", i, got[i], want)
		}
	}
	return nil
}

func (ap *applier) put() {
	k, v, l := genKey(ap.r), ap.val(), ap.genLease()
	a := ap.clk.now()
	rev := ap.kv.Put(k, []byte(v), lease.LeaseID(l))
	ap.step("Put", a, func(m *model) error {
		t := m.begin()
		t.put(string(k), v, l)
		t.commit()
		return expect(rev == m.rev(), "Put returned %d, want %d", rev, m.rev())
	})
}

func (ap *applier) deleteRange() {
	key, end := genKey(ap.r), genEnd(ap.r)
	a := ap.clk.now()
	n, rev := ap.kv.DeleteRange(key, end)
	ap.step("DeleteRange", a, func(m *model) error {
		t := m.begin()
		want := t.del(key, end)
		t.commit()
		return expect(n == want && rev == m.rev(), "DeleteRange(%q, %q) returned %d %d, want %d %d", key, end, n, rev, want, m.rev())
	})
}

// compact compacts at a revision from 1 to one past the current one.
func (ap *applier) compact() {
	c := 1 + ap.r.Int64N(ap.hint()+1)
	a := ap.clk.now()
	ch, err := ap.kv.Compact(traceutil.TODO(), c)
	what := fmt.Sprintf("Compact(%d)", c)
	if ch != nil {
		ap.chans = append(ap.chans, compactChan{ch, ap.restores, what})
	}
	ap.step(what, a, func(m *model) error {
		switch {
		case c <= m.compact:
			return expect(err == mvcc.ErrCompacted && ch != nil, "%s at compaction %d: %v", what, m.compact, err)
		case c > m.rev():
			return expect(err == mvcc.ErrFutureRev && ch == nil, "%s at revision %d: %v", what, m.rev(), err)
		}
		m.compactions = append(m.compactions, compaction{c, m.compact})
		m.compact = c
		return expect(err == nil && ch != nil, "%s: %v", what, err)
	})
}

// restore restores the store from its own backend (as a restart would, without stopping it).
func (ap *applier) restore() {
	a := ap.clk.now()
	err := ap.kv.Restore(ap.be)
	ap.restores++
	ap.steps = append(ap.steps, step{what: "Restore", a: a, b: ap.clk.now(), restore: true,
		apply: func(m *model) error { return expect(err == nil, "Restore: %v", err) }})
}

func (ap *applier) hash() {
	a := ap.clk.now()
	_, rev, err := ap.kv.HashStorage().Hash()
	ap.observe("Hash", a, func(m *model, p point) error {
		return expect(err == nil && rev == p.rev, "Hash at %+v: revision %d, %v", p, rev, err)
	})
}

func (ap *applier) grant() {
	ap.nextID++
	id := ap.nextID
	a := ap.clk.now()
	_, err := ap.le.Grant(lease.LeaseID(id), 3600)
	ap.leases = append(ap.leases, id)
	ap.step("Grant", a, func(m *model) error { return expect(err == nil, "Grant(%d): %v", id, err) })
}

// revoke revokes a live lease: the lessor deletes its keys, in key order, in one revision.
func (ap *applier) revoke() {
	if len(ap.leases) == 0 {
		return
	}
	i := ap.r.IntN(len(ap.leases))
	id := ap.leases[i]
	ap.leases = slices.Delete(ap.leases, i, i+1)
	a := ap.clk.now()
	err := ap.le.Revoke(lease.LeaseID(id))
	ap.step("Revoke", a, func(m *model) error {
		t := m.begin()
		for _, k := range allKeys {
			if e, ok := t.st[k]; ok && e.lease == id {
				t.del([]byte(k), nil)
			}
		}
		t.commit()
		return expect(err == nil, "Revoke(%d): %v", id, err)
	})
}

// checkLeases checks the lessor's record of each key's lease, which mvcc's puts and deletes keep.
func (ap *applier) checkLeases() {
	a := ap.clk.now()
	got := map[string]int64{}
	for _, k := range allKeys {
		got[k] = int64(ap.le.GetLease(lease.LeaseItem{Key: k}))
	}
	keys := map[int64][]string{}
	for _, id := range ap.leases {
		if l := ap.le.Lookup(lease.LeaseID(id)); l != nil {
			keys[id] = l.Keys()
			sort.Strings(keys[id])
		}
	}
	live := slices.Clone(ap.leases)
	ap.observe("lessor", a, func(m *model, p point) error { return checkLessor(m.states[p.rev], live, got, keys) })
}

func checkLessor(st map[string]kvRec, live []int64, got map[string]int64, keys map[int64][]string) error {
	want := map[int64][]string{}
	for _, id := range live {
		want[id] = nil
	}
	for _, k := range allKeys {
		if got[k] != st[k].lease {
			return fmt.Errorf("lessor: key %q has lease %d, want %d", k, got[k], st[k].lease)
		}
		if st[k].lease != 0 {
			want[st[k].lease] = append(want[st[k].lease], k)
		}
	}
	for id, ks := range want {
		if _, ok := keys[id]; !ok || !slices.Equal(keys[id], ks) {
			return fmt.Errorf("lessor: lease %d has keys %q, want %q", id, keys[id], ks)
		}
	}
	return nil
}

// ---------------------------------------------------------------------------------------------
// Readers.

// readTxn runs a read transaction (in either mode, possibly wrapped by NewReadOnlyTxnWrite) of one
// to three ranges.
func readTxn(kv mvcc.KV, r *rand.Rand, clk *clock, hint int64) obs {
	mode := mvcc.ConcurrentReadTxMode
	if r.IntN(2) == 0 {
		mode = mvcc.SharedBufReadTxMode
	}
	wrap := r.IntN(2) == 0
	a := clk.now()
	tr := kv.Read(mode, traceutil.TODO())
	if wrap {
		tr = mvcc.NewReadOnlyTxnWrite(tr)
	}
	rev, first := tr.Rev(), tr.FirstRev()
	var qs []rangeReq
	var ress []*mvcc.RangeResult
	var errs []error
	for range 1 + r.IntN(3) {
		q := genRange(r, hint)
		res, err := tr.Range(context.TODO(), q.key, q.end, q.ro)
		qs, ress, errs = append(qs, q), append(ress, res), append(errs, err)
	}
	changes := 0
	if wrap {
		changes = len(tr.(mvcc.TxnWrite).Changes())
	}
	tr.End()
	return obs{"read txn", a, clk.now(), func(m *model, p point) error {
		if rev != p.rev || first != p.compact || changes != 0 {
			return fmt.Errorf("read txn: Rev %d FirstRev %d (%d changes) at %+v", rev, first, changes, p)
		}
		for i, q := range qs {
			if err := checkRange(func(r int64) map[string]kvRec { return m.states[r] }, rev, first, q, ress[i], errs[i]); err != nil {
				return err
			}
		}
		return nil
	}}
}

type reader struct {
	kv   mvcc.KV
	r    *rand.Rand
	clk  *clock
	obs  []obs
	hint int64
}

func (rd *reader) observe(what string, a int64, ok func(m *model, p point) error) {
	rd.obs = append(rd.obs, obs{what, a, rd.clk.now(), ok})
}

func (rd *reader) run(done *atomic.Bool) {
	for !done.Load() {
		switch rd.r.IntN(7) {
		case 0, 1:
			rd.obs = append(rd.obs, readTxn(rd.kv, rd.r, rd.clk, rd.hint))
		case 2:
			q := genRange(rd.r, rd.hint)
			a := rd.clk.now()
			res, err := rd.kv.Range(context.TODO(), q.key, q.end, q.ro)
			rd.observe("Range", a, func(m *model, p point) error {
				return checkRange(func(r int64) map[string]kvRec { return m.states[r] }, p.rev, p.compact, q, res, err)
			})
		case 3:
			a := rd.clk.now()
			rev := rd.kv.Rev()
			rd.hint = rev
			rd.observe("Rev", a, func(m *model, p point) error { return expect(rev == p.rev, "Rev %d at %+v", rev, p) })
		case 4:
			a := rd.clk.now()
			first := rd.kv.FirstRev()
			rd.observe("FirstRev", a, func(m *model, p point) error {
				return expect(first == p.compact, "FirstRev %d at %+v", first, p)
			})
		case 5:
			q := genRev(rd.r, rd.hint)
			a := rd.clk.now()
			h, cur, err := rd.kv.HashStorage().HashByRev(q)
			rd.observe("HashByRev", a, func(m *model, p point) error { return m.checkHashByRev(p, q, h, cur, err) })
		default:
			a := rd.clk.now()
			hs := rd.kv.HashStorage().Hashes()
			rd.observe("Hashes", a, func(m *model, p point) error { return m.checkHashes(p, hs) })
		}
	}
}

// ---------------------------------------------------------------------------------------------
// Watch streams.

type opKind int

const (
	opWatch opKind = iota
	opCancel
	opProgress
	opProgressAll
	opRev
	opClose
)

// A streamOp is a call its owner made on a stream.
type streamOp struct {
	kind     opKind
	a, b     int64
	id       mvcc.WatchID // Watch's requested ID (0: auto), Cancel's and RequestProgress's
	key, end []byte
	start    int64
	filter   int
	gotID    mvcc.WatchID
	err      error
	ok       bool  // RequestProgressAll's result
	rev      int64 // Rev's result
}

// A streamLog is a stream's history: its owner's calls, and the responses it delivered.
type streamLog struct {
	ops   []streamOp
	mu    sync.Mutex
	resps []mvcc.WatchResponse
	done  chan struct{} // closed once the stream's channel is closed and drained
}

// Filters: none, no puts, no deletes.
var filters = [][]mvcc.FilterFunc{
	nil,
	{func(e *mvccpb.Event) bool { return e.Type == mvccpb.Event_PUT }},
	{func(e *mvccpb.Event) bool { return e.Type == mvccpb.Event_DELETE }},
}

// explicitIDs are where explicitly chosen watch IDs start, far above auto-assigned ones, so that
// no ID is used twice on a stream.
const explicitIDs = 1 << 40

type streamOwner struct {
	kv    mvcc.WatchableKV
	r     *rand.Rand
	clk   *clock
	logs  []*streamLog
	ws    mvcc.WatchStream
	live  []mvcc.WatchID
	next  mvcc.WatchID // next explicit ID
	hint  int64
	ended bool // the current stream was closed by Close
}

func (o *streamOwner) open() {
	o.ws = o.kv.NewWatchStream()
	l := &streamLog{done: make(chan struct{})}
	o.logs = append(o.logs, l)
	o.live, o.next = nil, explicitIDs
	go func(ch <-chan mvcc.WatchResponse) {
		for resp := range ch {
			l.mu.Lock()
			l.resps = append(l.resps, resp)
			l.mu.Unlock()
		}
		close(l.done)
	}(o.ws.Chan())
}

func (o *streamOwner) record(op streamOp) {
	l := o.logs[len(o.logs)-1]
	l.ops = append(l.ops, op)
}

// liveID returns a live watcher's ID, or (half the time, or with none live) one never used.
func (o *streamOwner) liveID() mvcc.WatchID {
	if len(o.live) == 0 || o.r.IntN(2) == 0 {
		return explicitIDs - 1
	}
	return o.live[o.r.IntN(len(o.live))]
}

func (o *streamOwner) run(done *atomic.Bool) {
	o.open()
	for !done.Load() {
		var op streamOp
		switch o.r.IntN(15) {
		case 0, 1, 2, 3, 4:
			op = streamOp{kind: opWatch, key: genKey(o.r), end: genEnd(o.r), filter: o.r.IntN(len(filters))}
			switch o.r.IntN(4) {
			case 0:
				op.id = o.next
				o.next++
			case 1: // a live watcher's ID: a duplicate
				if len(o.live) > 0 {
					op.id = o.live[o.r.IntN(len(o.live))]
				}
			}
			if o.r.IntN(3) > 0 {
				op.start = genRev(o.r, o.hint)
			}
			op.a = o.clk.now()
			op.gotID, op.err = o.ws.Watch(context.TODO(), op.id, op.key, op.end, op.start, filters[op.filter]...)
			if op.err == nil {
				o.live = append(o.live, op.gotID)
			}
		case 5, 6:
			op = streamOp{kind: opCancel, id: o.liveID()}
			op.a = o.clk.now()
			op.err = o.ws.Cancel(op.id)
			if i := slices.Index(o.live, op.id); i >= 0 {
				o.live = slices.Delete(o.live, i, i+1)
			}
		case 7, 8:
			op = streamOp{kind: opProgress, id: o.liveID()}
			op.a = o.clk.now()
			o.ws.RequestProgress(op.id)
		case 9, 10:
			op = streamOp{kind: opProgressAll}
			op.a = o.clk.now()
			op.ok = o.ws.RequestProgressAll()
		case 11, 12, 13:
			op = streamOp{kind: opRev}
			op.a = o.clk.now()
			op.rev = o.ws.Rev()
			o.hint = op.rev
		default:
			op = streamOp{kind: opClose}
			op.a = o.clk.now()
			o.ws.Close()
			op.b = o.clk.now()
			o.record(op)
			o.open()
			continue
		}
		op.b = o.clk.now()
		o.record(op)
	}
}

// ---------------------------------------------------------------------------------------------
// Checking.

type checker struct {
	m       *model
	epochs  []epoch
	watched map[string]watched // memoized newWatcher
}

// replay replays the applier's steps on a new model, recording an epoch at each change of point,
// and one for each Restore while it runs.
func replay(steps []step) (*checker, error) {
	m := newModel()
	c := &checker{m: m, epochs: []epoch{{m.point(), 0, 0}}, watched: map[string]watched{}}
	for _, s := range steps {
		if err := s.apply(m); err != nil {
			return nil, fmt.Errorf("%s: %v", s.what, err)
		}
		p := m.point()
		if s.restore {
			restoring := p
			restoring.restoring = true
			c.epochs = append(c.epochs, epoch{restoring, s.a, s.b})
		}
		if s.restore || p != c.epochs[len(c.epochs)-1].p {
			c.epochs = append(c.epochs, epoch{p, s.a, s.b})
		}
	}
	return c, nil
}

// points are the points that may have been current at some time between a and b: of an epoch
// whose step began before b, and whose successor's step did not end before a.
// (The applier's steps are sequential, so the epochs are ordered by both times.)
func (c *checker) points(a, b int64) []point {
	lo := sort.Search(len(c.epochs), func(j int) bool { return j+1 == len(c.epochs) || c.epochs[j+1].b >= a })
	hi := sort.Search(len(c.epochs), func(j int) bool { return c.epochs[j].a > b })
	var ps []point
	for _, e := range c.epochs[lo:max(lo, hi)] {
		ps = append(ps, e.p)
	}
	return ps
}

// check checks an observation: it must agree with the model at one of the points of its time.
func (c *checker) check(o obs) error {
	var first error
	for _, p := range c.points(o.a, o.b) {
		err := o.ok(c.m, p)
		if err == nil {
			return nil
		}
		if first == nil {
			first = err
		}
	}
	return fmt.Errorf("%s [%d, %d]: %v", o.what, o.a, o.b, first)
}

// A watcher is a successful Watch, with what its stream delivered to it so far.
type watcher struct {
	id       mvcc.WatchID
	key, end []byte
	filter   int
	start    int64
	// starts: the revisions its first event may have (its start revision, or, for a start of 0,
	// one past each revision the store may have had during the Watch call), narrowed to those
	// consistent with what it received
	starts    []int64
	events    []change // every change it watches, from revision 1, in order
	revs      []int64  // events[i]'s revision
	got       int      // how many it received
	compacted bool
	canceled  bool
}

// expectedFrom is the index in w.events of the first change at or after revision s.
func (w *watcher) expectedFrom(s int64) int {
	i, _ := slices.BinarySearch(w.revs, s)
	return i
}

// narrow keeps the start revisions s for which ok(i) holds, i the index of w's next expected
// event from s (events from s it has received: i - expectedFrom(s) == w.got).
func (w *watcher) narrow(ok func(i int) bool) bool {
	w.starts = slices.DeleteFunc(w.starts, func(s int64) bool { return !ok(w.expectedFrom(s) + w.got) })
	return len(w.starts) > 0
}

func (c *checker) newWatcher(op streamOp) *watcher {
	w := &watcher{id: op.gotID, key: op.key, end: op.end, filter: op.filter, start: op.start}
	if op.start > 0 {
		w.starts = []int64{op.start}
	} else {
		for _, p := range c.points(op.a, op.b) {
			if !slices.Contains(w.starts, p.rev+1) {
				w.starts = append(w.starts, p.rev+1)
			}
		}
	}
	ck := fmt.Sprintf("%q %q %v %d", op.key, op.end, op.end == nil, op.filter)
	if ev, ok := c.watched[ck]; ok {
		w.events, w.revs = ev.events, ev.revs
		return w
	}
	for r := int64(1); r <= c.m.rev(); r++ {
		for _, ch := range c.m.changes[r] {
			if inRange(op.key, op.end, ch.key) && !(op.filter == 1 && !ch.del) && !(op.filter == 2 && ch.del) {
				w.events, w.revs = append(w.events, ch), append(w.revs, r)
			}
		}
	}
	c.watched[ck] = watched{w.events, w.revs}
	return w
}

// watched is the changes a range and filter watch, from revision 1, and their revisions.
type watched struct {
	events []change
	revs   []int64
}

// receive checks an event against w's next expected one.
func (w *watcher) receive(ev *mvccpb.Event) error {
	ok := w.narrow(func(i int) bool {
		if i >= len(w.events) {
			return false
		}
		ch, r := w.events[i], w.revs[i]
		if ch.del {
			want := &mvccpb.KeyValue{Key: []byte(ch.key), ModRevision: r}
			return ev.Type == mvccpb.Event_DELETE && proto.Equal(ev.Kv, want) && ev.PrevKv == nil
		}
		return ev.Type == mvccpb.Event_PUT && checkKV(ev.Kv, ch.key, ch.kv, false) == nil && ev.PrevKv == nil
	})
	if !ok {
		return fmt.Errorf("watcher %d [%q, %q) filter %d start %d: event %d is %v, not the next change it watches", w.id, w.key, w.end, w.filter, w.start, w.got, ev)
	}
	w.got++
	return nil
}

// synced checks that w has received every change it watches up to revision rev.
func (w *watcher) synced(rev int64) bool {
	return w.narrow(func(i int) bool { return i >= len(w.events) || w.revs[i] > rev })
}

// checkStream checks a stream's history: its owner's calls, then its responses in order. With
// final, every watcher still live must have received every change it watches.
func (c *checker) checkStream(l *streamLog, final bool) (complete bool, err error) {
	all := map[mvcc.WatchID]*watcher{}
	var live []mvcc.WatchID
	nextAuto := mvcc.WatchID(0)
	type progressAll struct {
		op       streamOp
		watchers []*watcher
	}
	var progs []progressAll
	closed := false
	for _, op := range l.ops {
		switch op.kind {
		case opWatch:
			var want mvcc.WatchID
			var wantErr error
			switch {
			case len(op.end) != 0 && bytes.Compare(op.key, op.end) >= 0:
				want, wantErr = -1, mvcc.ErrEmptyWatcherRange
			case op.id != 0 && slices.Contains(live, op.id):
				want, wantErr = -1, mvcc.ErrWatcherDuplicateID
			case op.id != 0:
				want = op.id
			default:
				for slices.Contains(live, nextAuto) {
					nextAuto++
				}
				want = nextAuto
				nextAuto++
			}
			if op.gotID != want || op.err != wantErr {
				return false, fmt.Errorf("Watch(%d, %q, %q, %d): %d %v, want %d %v", op.id, op.key, op.end, op.start, op.gotID, op.err, want, wantErr)
			}
			if op.err == nil {
				all[op.gotID] = c.newWatcher(op)
				live = append(live, op.gotID)
			}
		case opCancel:
			i := slices.Index(live, op.id)
			if (i >= 0) != (op.err == nil) || i < 0 && op.err != mvcc.ErrWatcherNotExist {
				return false, fmt.Errorf("Cancel(%d): %v", op.id, op.err)
			}
			if i >= 0 {
				all[op.id].canceled = true
				live = slices.Delete(live, i, i+1)
			}
		case opProgressAll:
			if len(live) == 0 && !op.ok {
				return false, fmt.Errorf("RequestProgressAll with no watchers returned false")
			}
			if len(live) > 0 && op.ok {
				p := progressAll{op: op}
				for _, id := range live {
					p.watchers = append(p.watchers, all[id])
				}
				progs = append(progs, p)
			}
		case opRev:
			rev := op.rev
			if err := c.check(obs{"WatchStream.Rev", op.a, op.b, func(m *model, p point) error {
				return expect(rev == p.rev, "Rev %d at %+v", rev, p)
			}}); err != nil {
				return false, err
			}
		case opClose:
			closed = true
		}
	}

	l.mu.Lock()
	resps := slices.Clone(l.resps)
	l.mu.Unlock()
	np := 0
	for _, resp := range resps {
		if resp.WatchID == -1 { // RequestProgressAll's response (clientv3.InvalidWatchID)
			if np == len(progs) || len(resp.Events) != 0 || resp.CompactRevision != 0 {
				return false, fmt.Errorf("unexpected progress-all response %+v", resp)
			}
			p := progs[np]
			np++
			P := resp.Revision
			if err := c.check(obs{"RequestProgressAll", p.op.a, p.op.b, func(m *model, pt point) error {
				return expect(P == pt.rev, "progress-all revision %d at %+v", P, pt)
			}}); err != nil {
				return false, err
			}
			for _, w := range p.watchers {
				if !w.synced(P) || w.start > P {
					return false, fmt.Errorf("progress-all at %d before watcher %d received its changes up to it", P, w.id)
				}
			}
			continue
		}
		w := all[resp.WatchID]
		if w == nil || w.compacted {
			return false, fmt.Errorf("response %+v for no live watcher", resp)
		}
		switch {
		case resp.CompactRevision != 0:
			cr := resp.CompactRevision
			if len(resp.Events) != 0 || !slices.ContainsFunc(c.m.compactions, func(x compaction) bool { return x.rev == cr }) {
				return false, fmt.Errorf("watcher %d: bad compaction response %+v", w.id, resp)
			}
			// it is compacted only if the next revision it needs is below cr
			if !w.notPast(cr) {
				return false, fmt.Errorf("watcher %d: compaction response at %d, but it had received up to it", w.id, cr)
			}
			w.compacted = true
		case len(resp.Events) == 0:
			if !w.synced(resp.Revision) || w.start > resp.Revision {
				return false, fmt.Errorf("watcher %d: progress at %d before it received its changes up to it", w.id, resp.Revision)
			}
		default:
			last := resp.Events[len(resp.Events)-1].Kv.ModRevision
			for _, ev := range resp.Events {
				if err := w.receive(ev); err != nil {
					return false, err
				}
			}
			if resp.Revision < last {
				return false, fmt.Errorf("watcher %d: response revision %d below its event's %d", w.id, resp.Revision, last)
			}
			// a revision's events come in one response
			if !w.synced(last) {
				return false, fmt.Errorf("watcher %d: response %+v leaves out changes of revision %d", w.id, resp, last)
			}
		}
	}
	if final && np != len(progs) {
		return false, fmt.Errorf("%d RequestProgressAll calls returned true but sent no response", len(progs)-np)
	}
	complete = true
	if !closed {
		for _, id := range live {
			if w := all[id]; !w.compacted && !w.synced(c.m.rev()) {
				if final {
					return false, fmt.Errorf("watcher %d [%q, %q) filter %d start %d: received %d events, not all it watches", w.id, w.key, w.end, w.filter, w.start, w.got)
				}
				complete = false
			}
		}
	}
	return complete, nil
}

// streamsComplete says whether every live watcher has received every change it watches (or a
// stream's history is already wrong, which the final check reports).
func (c *checker) streamsComplete(owners []*streamOwner) bool {
	for _, o := range owners {
		if done, err := c.checkStream(o.logs[len(o.logs)-1], false); !done && err == nil {
			return false
		}
	}
	return true
}

// notPast keeps the start revisions s for which w had not yet received up to revision cr-1: its
// next revision to receive (s, or one past its last event) is below cr.
func (w *watcher) notPast(cr int64) bool {
	w.starts = slices.DeleteFunc(w.starts, func(s int64) bool {
		next := s
		if w.got > 0 {
			next = w.revs[w.expectedFrom(s)+w.got-1] + 1
		}
		return next >= cr
	})
	return len(w.starts) > 0
}

func expect(ok bool, format string, args ...any) error {
	if ok {
		return nil
	}
	return fmt.Errorf(format, args...)
}

// ---------------------------------------------------------------------------------------------
// The run.

// Run runs a test of cfg and returns the first failures found (none: nil).
func Run(cfg Config) error {
	lg := zap.NewNop()
	bcfg := backend.DefaultBackendConfig(lg)
	bcfg.Path = cfg.Path
	be := backend.New(bcfg)
	defer be.Close()
	lcfg := lease.LessorConfig{MinLeaseTTL: 1}
	le := lease.NewLessor(lg, be, nil, lcfg)
	kv := mvcc.New(lg, be, le, mvcc.StoreConfig{})
	clk := &clock{}

	ap := &applier{kv: kv, be: be, le: le, r: rand.New(rand.NewPCG(cfg.Seed, 0)), clk: clk}
	readers := make([]*reader, cfg.Readers)
	owners := make([]*streamOwner, cfg.Streams)
	// The readers and stream owners run until the applier is done.
	var wg sync.WaitGroup
	var done atomic.Bool
	wg.Go(func() {
		ap.run(cfg.ApplierOps)
		done.Store(true)
	})
	for i := range readers {
		readers[i] = &reader{kv: kv, r: rand.New(rand.NewPCG(cfg.Seed, uint64(1+i))), clk: clk, hint: 1}
		wg.Go(func() { readers[i].run(&done) })
	}
	for i := range owners {
		owners[i] = &streamOwner{kv: kv, r: rand.New(rand.NewPCG(cfg.Seed, uint64(1000+i))), clk: clk, hint: 1}
		wg.Go(func() { owners[i].run(&done) })
	}
	wg.Wait()

	var errs []error
	fail := func(err error) {
		if err != nil {
			errs = append(errs, err)
		}
	}
	c, err := replay(ap.steps)
	if err != nil {
		kv.Close()
		le.Stop()
		return err
	}
	deadline := time.Now().Add(cfg.Drain)

	// Every compaction after the last Restore finishes.
	for _, cc := range ap.chans {
		if cc.restores == ap.restores {
			select {
			case <-cc.ch:
			case <-time.After(time.Until(deadline)):
				fail(fmt.Errorf("%s: never finished", cc.what))
			}
		}
	}

	// Every live watcher receives every change it watches.
	for !c.streamsComplete(owners) && time.Now().Before(deadline) {
		time.Sleep(100 * time.Millisecond)
	}
	for _, o := range owners {
		o.ws.Close()
		for _, l := range o.logs {
			<-l.done
			_, err := c.checkStream(l, l == o.logs[len(o.logs)-1])
			fail(err)
		}
	}

	for _, o := range ap.obs {
		fail(c.check(o))
	}
	for _, rd := range readers {
		for _, o := range rd.obs {
			fail(c.check(o))
		}
	}

	// Quiescent, then after a restart: every revision read and hashed, and the leases.
	fail(c.checkAll("quiescent", kv, le, ap.leases))
	fail(kv.Close())
	le.Stop()
	le = lease.NewLessor(lg, be, nil, lcfg)
	kv = mvcc.New(lg, be, le, mvcc.StoreConfig{})
	fail(c.checkAll("restarted", kv, le, ap.leases))
	fail(kv.Close())
	le.Stop()

	if len(errs) > 5 {
		errs = append(errs[:5], fmt.Errorf("... and %d more", len(errs)-5))
	}
	return errors.Join(errs...)
}

// checkAll checks a store that nothing else uses against the model's last point: its revisions,
// every revision's key-values and hash, and the lessor's leases.
func (c *checker) checkAll(what string, kv mvcc.KV, le lease.Lessor, leases []int64) error {
	m, p := c.m, c.m.point()
	all := rangeReq{key: []byte{}, end: []byte{}}
	if rev, first := kv.Rev(), kv.FirstRev(); rev != p.rev || first != p.compact {
		return fmt.Errorf("%s: Rev %d FirstRev %d, want %+v", what, rev, first, p)
	}
	for r := max(p.compact, 1); r <= p.rev; r++ {
		all.ro.Rev = r
		res, err := kv.Range(context.TODO(), all.key, all.end, all.ro)
		if err := checkRange(func(r int64) map[string]kvRec { return m.states[r] }, p.rev, p.compact, all, res, err); err != nil {
			return fmt.Errorf("%s: %v", what, err)
		}
		h, cur, err := kv.HashStorage().HashByRev(r)
		if err := m.checkHashByRev(p, r, h, cur, err); err != nil {
			return fmt.Errorf("%s: %v", what, err)
		}
	}
	got := map[string]int64{}
	for _, k := range allKeys {
		got[k] = int64(le.GetLease(lease.LeaseItem{Key: k}))
	}
	keys := map[int64][]string{}
	for _, id := range leases {
		if l := le.Lookup(lease.LeaseID(id)); l != nil {
			keys[id] = l.Keys()
			sort.Strings(keys[id])
		}
	}
	if err := checkLessor(m.states[p.rev], leases, got, keys); err != nil {
		return fmt.Errorf("%s: %v", what, err)
	}
	return nil
}
