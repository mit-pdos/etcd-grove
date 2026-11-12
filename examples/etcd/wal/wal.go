// Package wal is a robustness tester of etcd's write-ahead log (go.etcd.io/etcd/server/v3/storage/
// wal) under crashes: Boot is one incarnation of a member's WAL, run again after every crash.
//
// Each incarnation does what etcd's bootstrap does with the WAL directory (a first start:
// TouchDirAll of the data and member directories, then wal.Create; a restart: wal.Exist,
// ValidSnapshotEntries, Open at the newest valid snapshot record, ReadAll, Repair once on a torn
// tail), checks what the restart read, then runs random WAL operations mixed as etcd's raft loop,
// apply thread and purge goroutine use the WAL (serialized):
//   - the raft loop's Saves: entries above the base (overwriting the uncommitted tail, or
//     re-sending entries an earlier incarnation saved, byte for byte, as a leader re-sends its log),
//     commit-only Saves (not synced), term and vote changes (synced); a received snapshot as
//     SaveSnapshot, then a Save of the hard state (commit at the snapshot) and entries above it,
//     then Sync;
//   - the apply thread's own snapshots: SaveSnapshot at or below the commit, ReleaseLockTo;
//   - the purge goroutine: rounds of fileutil.purgeFile's loop;
//   - Sync, a graceful Close followed by a restart, small segment sizes (cuts).
//
// # The check
//
// The reference is the WAL spec's: the history H (every Save and SaveSnapshot since Create, across
// incarnations), the synced mark n, the crash relation walImg H n and the relaxed reader
// walReadCut (ref.go): a restart reads walReadCut I k for an image I and a purged prefix k at most
// the model's purge position, which the tester bounds per candidate history (unl, pur: the
// model's name bound at each ReleaseLockTo and Open, raised into pur before each purge round; WAL
// W4c). A restart that finds no WAL after Create returned, or reads a state that is walReadCut of
// no image of walImg H n within the bound, panics. A restart that fails (bootstrap's error return or Fatal) ends the run: the
// member is down, which the spec allows. The reference state is kept in a durable file (oracle.go),
// written before each operation (the history with the operation) and after each syncing return
// (the mark), so a crash at any point leaves a reference the restart can be checked against.
// After a restart the history is the image read, which the tester only knows up to the restart's
// result: it keeps every image consistent with it (the candidates).
//
// The theorem to prove (etcd_wal_safe, with etcd_wal_adequate) is that Boot never panics, over
// the WAL's trusted spec. The crash driver (crashtest/) runs it under a recorded file system with
// power-loss and kill images between incarnations.
package wal

import (
	"os"
	"strings"

	"github.com/goose-lang/primitive"
	"go.uber.org/zap"

	"go.etcd.io/etcd/client/pkg/v3/fileutil"
	etcdwal "go.etcd.io/etcd/server/v3/storage/wal"
	"go.etcd.io/etcd/server/v3/storage/wal/walpb"
	"go.etcd.io/raft/v3/raftpb"
)

// maxIndex bounds the indices the tester saves (and its terms): Save and SaveSnapshot take
// indices below 2^64-1 (WAL W4a.2), and nameBound's index+1 must not wrap (WAL W4c, T-4).
const maxIndex uint64 = 1 << 62

// Boot's results (a panic is the only failure).
const (
	// StatusRan: the incarnation started (first start or a checked restart) and ran its operations.
	StatusRan uint64 = 0
	// StatusDown: the restart's read failed (the member stays down), or a WAL call failed (the raft
	// loop Fatals).
	StatusDown uint64 = 1
)

// rnd is the source of every choice: primitive.RandomUint64 (any value), or, when seeded, a
// xorshift sequence (so that the crash driver reproduces a run from its seed).
type rnd struct {
	seeded bool
	x      uint64
}

func newRnd(seed uint64) *rnd {
	return &rnd{seeded: seed != 0, x: seed}
}

func (r *rnd) next() uint64 {
	if !r.seeded {
		return primitive.RandomUint64()
	}
	x := r.x
	x = x ^ (x << 13)
	x = x ^ (x >> 7)
	x = x ^ (x << 17)
	r.x = x
	return x
}

// choose returns a number in [0, n) (0 if n is 0).
func (r *rnd) choose(n uint64) uint64 {
	if n == 0 {
		return 0
	}
	return r.next() % n
}

// entData is an entry's data: size bytes, the salt's 8 bytes first, then a pattern of the index,
// the term and the position.
func entData(e entry) []byte {
	b := make([]byte, 0, e.size)
	for i := uint64(0); i < 8 && i < e.size; i++ {
		b = append(b, byte(e.salt>>(8*i)))
	}
	for i := uint64(8); i < e.size; i++ {
		b = append(b, byte((e.index+3*e.term+i)%251))
	}
	return b
}

func newU64(x uint64) *uint64 {
	return &x
}

func toRaft(e entry) *raftpb.Entry {
	return &raftpb.Entry{Index: newU64(e.index), Term: newU64(e.term), Type: raftpb.EntryType_EntryNormal.Enum(), Data: entData(e)}
}

// fromRaft reads an entry back; data that is not entData of its own index, term, size and salt
// gives size 0, which no saved entry has (sizes are at least 16).
func fromRaft(re *raftpb.Entry) entry {
	d := re.GetData()
	var salt uint64
	for i := 0; i < 8 && i < len(d); i++ {
		salt = salt | uint64(d[i])<<(8*uint64(i))
	}
	e := entry{index: re.GetIndex(), term: re.GetTerm(), size: uint64(len(d)), salt: salt}
	want := entData(e)
	for i := 0; i < len(d); i++ {
		if d[i] != want[i] {
			e.size = 0
		}
	}
	return e
}

func toHS(h hardState) *raftpb.HardState {
	return &raftpb.HardState{Term: newU64(h.term), Vote: newU64(h.vote), Commit: newU64(h.commit)}
}

// The outcomes of restartRead.
const (
	readOK   uint64 = 0
	readFail uint64 = 1
)

// restartRead is bootstrap's restart path on walDir (wal.Exist is checked by the caller):
// recoverSnapshot's ValidSnapshotEntries and newest snapshot record, then openWALFromSnapshot's
// Open, ReadAll, and Repair once on a failed ReadAll. On success the WAL is open, ready to append.
// When m is not nil, the snapshot each Open opens at is added to m's oracle (opens) before the
// Open, since the Open unlocks the files before it (the model's unl).
//
// Differences from bootstrap, for the proof (WAL W4c, T-2, T-3, T-5): Repair is tried on any
// ReadAll error, not only io.ErrUnexpectedEOF (on another error the retried read fails the same
// way, so the read fails, as bootstrap's Fatal); a failed Close of the failed handle fails the
// read; no valid snapshot pair fails the read.
func restartRead(lg *zap.Logger, walDir string, m *member) (uint64, contents, *etcdwal.WAL) {
	var c contents
	snaps, err := etcdwal.ValidSnapshotEntries(lg, walDir)
	if err != nil {
		return readFail, c, nil
	}
	if len(snaps) == 0 {
		return readFail, c, nil
	}
	var idx uint64
	var term uint64
	for i := 0; i < len(snaps); i++ {
		if *snaps[i].Index >= idx {
			idx = *snaps[i].Index
			term = *snaps[i].Term
		}
	}
	repaired := false
	for {
		if m != nil {
			m.o.opens = append(m.o.opens, idx)
			storeOracle(m.orPath, m.o)
		}
		w, err2 := etcdwal.Open(lg, walDir, &walpb.Snapshot{Index: newU64(idx), Term: newU64(term)})
		if err2 != nil {
			return readFail, c, nil
		}
		_, st, ents, err3 := w.ReadAll()
		if err3 == nil {
			c.hs = hardState{term: st.GetTerm(), vote: st.GetVote(), commit: st.GetCommit()}
			c.baseIdx = idx
			c.baseTerm = term
			c.ents = make([]entry, 0)
			for i := 0; i < len(ents); i++ {
				c.ents = append(c.ents, fromRaft(ents[i]))
			}
			return readOK, c, w
		}
		if w.Close() != nil {
			return readFail, c, nil
		}
		if repaired {
			return readFail, c, nil
		}
		if !etcdwal.Repair(lg, walDir) {
			return readFail, c, nil
		}
		repaired = true
	}
}

// addCand adds the candidate (img, unl, pur) to cs, merging the bounds (max) with an equal history.
func addCand(cs []cand, img []walOp, unl uint64, pur uint64) []cand {
	for j := 0; j < len(cs); j++ {
		if histEq(cs[j].h, img) {
			if unl > cs[j].unl {
				cs[j].unl = unl
			}
			if pur > cs[j].pur {
				cs[j].pur = pur
			}
			return cs
		}
	}
	return append(cs, cand{h: img, unl: unl, pur: pur})
}

// checkRestart is the check: the restart read c; some image of some candidate's history, at or
// past its synced mark, read from a purged prefix k at most the candidate's purge bound, must read
// c (the spec's relaxed reader walReadCut, the crash's k <= min(pur, |I|)). The images that do
// are the candidates from now on, with the candidate's purge bound and an unlock bound raised by
// the Opens since the last restart (each Open unlocks below nameBound of an image of the history).
func checkRestart(o oracle, c contents) oracle {
	next := make([]cand, 0)
	for ci := 0; ci < len(o.cands); ci++ {
		cd := o.cands[ci]
		h := copyOps(cd.h)
		for i := 0; i < len(o.since); i++ {
			h = append(h, o.since[i])
		}
		n := len(cd.h) + int(o.synced)
		imgs := walImgs(h, n)
		unl := cd.unl
		for si := 0; si < len(o.opens); si++ {
			b := openBound(imgs, o.opens[si])
			if b > unl {
				unl = b
			}
		}
		for k := 0; k < len(imgs); k++ {
			kmax := cd.pur
			if kmax > uint64(len(imgs[k])) {
				kmax = uint64(len(imgs[k]))
			}
			for kk := uint64(0); kk <= kmax; kk++ {
				rc, ok := walReadCut(imgs[k], kk)
				if ok && contentsEq(rc, c) {
					next = addCand(next, imgs[k], unl, cd.pur)
					break
				}
			}
		}
	}
	if len(next) == 0 {
		panic("walrobust: the restart read a state that no crash image of the history gives")
	}
	return oracle{created: true, cands: next, since: make([]walOp, 0), synced: 0, lastHS: c.hs, opens: make([]uint64, 0)}
}

// purgeRound is one round of fileutil.purgeFile's loop on the WAL directory (the server's WAL
// purge, suffix "wal", keeping max files): the oldest files beyond max removed, each only if its
// lock can be taken.
func purgeRound(lg *zap.Logger, dir string, max uint64) {
	names, err := fileutil.ReadDir(dir)
	if err != nil {
		return
	}
	fs := make([]string, 0)
	for i := 0; i < len(names); i++ {
		if strings.HasSuffix(names[i], "wal") {
			fs = append(fs, names[i])
		}
	}
	for n := uint64(0); n+max < uint64(len(fs)); n++ {
		f := dir + "/" + fs[n]
		l, err2 := fileutil.TryLockFile(f, os.O_WRONLY, fileutil.PrivateFileMode)
		if err2 != nil {
			return
		}
		if os.Remove(f) != nil {
			l.Close()
			return
		}
		l.Close()
	}
}

// member is one incarnation's state: the open WAL, the reference, and the raft-like state the
// operations are generated from.
type member struct {
	lg     *zap.Logger
	r      *rnd
	orPath string
	walDir string
	w      *etcdwal.WAL
	o      oracle
	term   uint64
	vote   uint64
	commit uint64
	base   uint64
	last   uint64
	terms  map[uint64]uint64
}

// resume sets the raft-like state from what the restart read (raft's state after RestartNode).
func (m *member) resume(c contents) {
	m.term = c.hs.term
	if m.term == 0 {
		m.term = 1
	}
	m.vote = c.hs.vote
	m.base = c.baseIdx
	m.last = c.baseIdx
	m.terms = make(map[uint64]uint64)
	m.terms[c.baseIdx] = c.baseTerm
	for i := 0; i < len(c.ents); i++ {
		m.terms[c.ents[i].index] = c.ents[i].term
		m.last = c.ents[i].index
	}
	m.commit = c.hs.commit
	if m.commit > m.last {
		m.commit = m.last
	}
}

func (m *member) hs() hardState {
	return hardState{term: m.term, vote: m.vote, commit: m.commit}
}

func (m *member) size() uint64 {
	k := m.r.choose(50)
	if k == 0 {
		return 70000 + m.r.choose(70000) // two exceed the WAL's 128 KiB write buffer
	}
	if k < 12 {
		return 16 + m.r.choose(40)
	}
	if k < 24 {
		return 400 + m.r.choose(800)
	}
	return 50 + m.r.choose(300)
}

// save is a Save: the operation added to the reference, then the call, then the mark moved if
// the Save syncs. False if the call failed.
func (m *member) save(h hardState, es []entry) bool {
	if hsEmpty(h) && len(es) == 0 {
		return true
	}
	m.o.since = append(m.o.since, walOp{hs: h, ents: es})
	storeOracle(m.orPath, m.o)
	res := make([]*raftpb.Entry, 0, len(es))
	for i := 0; i < len(es); i++ {
		res = append(res, toRaft(es[i]))
	}
	if m.w.Save(toHS(h), res) != nil {
		return false
	}
	if walMustSync(m.o.lastHS, h, len(es)) {
		m.o.synced = uint64(len(m.o.since))
		storeOracle(m.orPath, m.o)
	}
	m.o.lastHS = phsNext(m.o.lastHS, h)
	return true
}

func (m *member) saveSnap(idx uint64, term uint64) bool {
	m.o.since = append(m.o.since, walOp{snap: true, idx: idx, term: term})
	storeOracle(m.orPath, m.o)
	cs := &raftpb.ConfState{Voters: []uint64{1}}
	if m.w.SaveSnapshot(&walpb.Snapshot{Index: newU64(idx), Term: newU64(term), ConfState: cs}) != nil {
		return false
	}
	m.o.synced = uint64(len(m.o.since))
	storeOracle(m.orPath, m.o)
	return true
}

func (m *member) sync() bool {
	if m.w.Sync() != nil {
		return false
	}
	m.o.synced = uint64(len(m.o.since))
	storeOracle(m.orPath, m.o)
	return true
}

func (m *member) close() bool {
	err := m.w.Close()
	m.w = nil
	if err != nil {
		return false
	}
	m.o.synced = uint64(len(m.o.since))
	storeOracle(m.orPath, m.o)
	return true
}

// restart is the restart path and its check; false if the read failed.
func (m *member) restart() bool {
	st, c, w := restartRead(m.lg, m.walDir, m)
	if st != readOK {
		return false
	}
	m.o = checkRestart(m.o, c)
	storeOracle(m.orPath, m.o)
	m.w = w
	m.resume(c)
	return true
}

// opEntries saves 1..4 entries at the current term: after the last, or overwriting the
// uncommitted tail; with the commit possibly advanced.
func (m *member) opEntries() bool {
	if m.last >= maxIndex {
		return true
	}
	floor := m.commit
	if m.base > floor {
		floor = m.base
	}
	lo := m.last + 1
	if m.last > floor && m.r.choose(4) == 0 {
		lo = floor + 1 + m.r.choose(m.last-floor)
	}
	n := 1 + m.r.choose(4)
	es := make([]entry, 0)
	for i := lo; i < lo+n; i++ {
		es = append(es, entry{index: i, term: m.term, size: m.size(), salt: m.r.next()})
		m.terms[i] = m.term
	}
	for i := lo + n; i <= m.last; i++ {
		delete(m.terms, i)
	}
	m.last = lo + n - 1
	if m.r.choose(2) == 0 && m.last > m.commit {
		m.commit = m.commit + m.r.choose(m.last-m.commit+1)
	}
	return m.save(m.hs(), es)
}

// opResend re-sends, byte for byte, entries after the last that the history holds (in the first
// candidate's history: entries saved before a crash and not read back), as a leader re-sends its
// log to a follower that lost them.
func (m *member) opResend() bool {
	if m.last >= maxIndex {
		return true
	}
	h := copyOps(m.o.cands[0].h)
	for i := 0; i < len(m.o.since); i++ {
		h = append(h, m.o.since[i])
	}
	f := walFold(h)
	if f.baseIdx > m.last {
		return true
	}
	start := m.last - f.baseIdx // f.ents[start] has index last+1
	if start >= uint64(len(f.ents)) {
		return true
	}
	es := make([]entry, 0)
	for i := start; i < uint64(len(f.ents)) && i < start+3; i++ {
		e := f.ents[i]
		if e.index != m.last+1+(i-start) {
			break
		}
		es = append(es, e)
	}
	if len(es) == 0 {
		return true
	}
	for i := 0; i < len(es); i++ {
		if es[i].term > m.term {
			m.term = es[i].term
		}
		m.terms[es[i].index] = es[i].term
	}
	m.last = es[len(es)-1].index
	return m.save(m.hs(), es)
}

// opCommit is a commit-only Save (not synced).
func (m *member) opCommit() bool {
	if m.last <= m.commit {
		return true
	}
	m.commit = m.commit + 1 + m.r.choose(m.last-m.commit)
	return m.save(m.hs(), make([]entry, 0))
}

// opTerm is a term (and vote) change (synced).
func (m *member) opTerm() bool {
	if m.term < maxIndex {
		m.term = m.term + 1
	}
	m.vote = m.r.choose(3)
	return m.save(m.hs(), make([]entry, 0))
}

// opOwnSnap is the apply thread's snapshot at or below the commit, its ReleaseLockTo, and
// possibly a purge round. Before ReleaseLockTo(a), every candidate's unlock bound is raised to
// nameBound of its history at a (ReleaseLockTo unlocks below it); before the purge round, every
// candidate's purge bound is raised to its unlock bound (the round deletes only unlocked files).
func (m *member) opOwnSnap() bool {
	if m.commit <= m.base {
		return true
	}
	a := m.base + 1 + m.r.choose(m.commit-m.base)
	if !m.saveSnap(a, m.terms[a]) {
		return false
	}
	for ci := 0; ci < len(m.o.cands); ci++ {
		h := copyOps(m.o.cands[ci].h)
		for i := 0; i < len(m.o.since); i++ {
			h = append(h, m.o.since[i])
		}
		b := nameBound(h, a)
		if b > m.o.cands[ci].unl {
			m.o.cands[ci].unl = b
		}
	}
	storeOracle(m.orPath, m.o)
	if m.w.ReleaseLockTo(a) != nil {
		return false
	}
	if m.r.choose(2) == 0 {
		for ci := 0; ci < len(m.o.cands); ci++ {
			if m.o.cands[ci].unl > m.o.cands[ci].pur {
				m.o.cands[ci].pur = m.o.cands[ci].unl
			}
		}
		storeOracle(m.orPath, m.o)
		purgeRound(m.lg, m.walDir, 1+m.r.choose(3))
	}
	m.base = a
	return true
}

// opRecvSnap is the raft loop's persistence of a Ready with a snapshot received from the leader:
// SaveSnapshot, then the Save of the hard state (commit at the snapshot) and the Ready's entries
// above it, then Sync.
func (m *member) opRecvSnap() bool {
	if m.last >= maxIndex {
		return true
	}
	s := m.last + 1 + m.r.choose(4)
	if !m.saveSnap(s, m.term) {
		return false
	}
	m.base = s
	m.last = s
	m.commit = s
	m.terms = make(map[uint64]uint64)
	m.terms[s] = m.term
	es := make([]entry, 0)
	k := m.r.choose(3)
	for i := s + 1; i <= s+k; i++ {
		es = append(es, entry{index: i, term: m.term, size: m.size(), salt: m.r.next()})
		m.terms[i] = m.term
		m.last = i
	}
	if !m.save(m.hs(), es) {
		return false
	}
	return m.sync()
}

// step runs one random operation; false if the member went down.
func (m *member) step() bool {
	k := m.r.choose(100)
	if k < 30 {
		return m.opEntries()
	}
	if k < 35 {
		return m.opResend()
	}
	if k < 50 {
		return m.opCommit()
	}
	if k < 58 {
		return m.opTerm()
	}
	if k < 70 {
		return m.opOwnSnap()
	}
	if k < 80 {
		return m.opRecvSnap()
	}
	if k < 90 {
		return m.sync()
	}
	if k < 95 {
		if !m.close() {
			return false
		}
		return m.restart()
	}
	return true
}

// Boot is one incarnation on the directory root (which holds oracle/, an existing directory, and
// the member's data/): the first start or the checked restart, then nOps operations, then possibly
// a graceful Close. seed 0 takes every choice from primitive.RandomUint64.
func Boot(root string, seed uint64, nOps uint64) uint64 {
	m := &member{lg: zap.NewNop(), r: newRnd(seed), orPath: root + "/oracle/state"}
	m.o = loadOracle(m.orPath)
	data := root + "/data"
	memberDir := data + "/member"
	m.walDir = memberDir + "/wal"
	if !etcdwal.Exist(m.walDir) {
		if m.o.created {
			panic("walrobust: the WAL vanished after wal.Create returned")
		}
		if fileutil.TouchDirAll(m.lg, data) != nil || fileutil.TouchDirAll(m.lg, memberDir) != nil {
			return StatusDown
		}
		w, err := etcdwal.Create(m.lg, m.walDir, []byte("m"))
		if err != nil {
			return StatusDown
		}
		m.w = w
		m.o = freshOracle()
		m.o.created = true
		storeOracle(m.orPath, m.o)
		var c contents
		m.resume(c)
	} else {
		if !m.restart() {
			return StatusDown
		}
	}
	for i := uint64(0); i < nOps; i++ {
		if !m.step() {
			return StatusDown
		}
	}
	if m.r.choose(2) == 0 {
		if !m.close() {
			return StatusDown
		}
	}
	return StatusRan
}

// Main is the program: incarnations of Boot on root, every choice any value. The crash and
// restart between incarnations are the machine's (the adequacy theorem's crash semantics).
func Main(root string) {
	Boot(root, 0, 40)
}
