package wal

// The reference model: the WAL spec's pure vocabulary (the Scope's §2.1, W0's walref), over this
// package's own record view. Everything here is pure: plain structs, slices and loops.

// hardState is raftpb.HardState.
type hardState struct {
	term   uint64
	vote   uint64
	commit uint64
}

func hsEmpty(h hardState) bool {
	return h.term == 0 && h.vote == 0 && h.commit == 0
}

func hsEq(a hardState, b hardState) bool {
	return a.term == b.term && a.vote == b.vote && a.commit == b.commit
}

// entry is a raft entry whose data is entData(index, term, size, salt).
type entry struct {
	index uint64
	term  uint64
	size  uint64
	salt  uint64
}

func entEq(a entry, b entry) bool {
	return a.index == b.index && a.term == b.term && a.size == b.size && a.salt == b.salt
}

// walOp is one WAL operation of the history: Save(hs, ents) or SaveSnapshot(idx, term).
type walOp struct {
	snap bool
	hs   hardState
	ents []entry
	idx  uint64
	term uint64
}

// contents is StorContents as a restart returns it: the base (the snapshot it opened at), the hard
// state, the entries above the base.
type contents struct {
	hs       hardState
	baseIdx  uint64
	baseTerm uint64
	ents     []entry
}

func contentsEq(a contents, b contents) bool {
	if !hsEq(a.hs, b.hs) || a.baseIdx != b.baseIdx || a.baseTerm != b.baseTerm || len(a.ents) != len(b.ents) {
		return false
	}
	for i := 0; i < len(a.ents); i++ {
		if !entEq(a.ents[i], b.ents[i]) {
			return false
		}
	}
	return true
}

func copyEnts(es []entry) []entry {
	out := make([]entry, 0, len(es))
	for i := 0; i < len(es); i++ {
		out = append(out, es[i])
	}
	return out
}

func copyOps(h []walOp) []walOp {
	out := make([]walOp, 0, len(h))
	for i := 0; i < len(h); i++ {
		out = append(out, h[i])
	}
	return out
}

func opEq(a walOp, b walOp) bool {
	if a.snap != b.snap || a.idx != b.idx || a.term != b.term || !hsEq(a.hs, b.hs) || len(a.ents) != len(b.ents) {
		return false
	}
	for i := 0; i < len(a.ents); i++ {
		if !entEq(a.ents[i], b.ents[i]) {
			return false
		}
	}
	return true
}

func histEq(a []walOp, b []walOp) bool {
	if len(a) != len(b) {
		return false
	}
	for i := 0; i < len(a); i++ {
		if !opEq(a[i], b[i]) {
			return false
		}
	}
	return true
}

// phsNext: an empty hard state leaves the previous one.
func phsNext(p hardState, h hardState) hardState {
	if hsEmpty(h) {
		return p
	}
	return h
}

// walLastHS is the last saved hard state (the WAL's w.state; what ReadAll returns).
func walLastHS(h []walOp) hardState {
	var p hardState
	for i := 0; i < len(h); i++ {
		if !h[i].snap {
			p = phsNext(p, h[i].hs)
		}
	}
	return p
}

// walMustSync is raft.MustSync against the last saved hard state: Save syncs before returning.
func walMustSync(last hardState, h hardState, nents int) bool {
	return nents > 0 || (!hsEmpty(h) && (h.vote != last.vote || h.term != last.term))
}

// walSaveSnap is walSaveSnap: a snapshot record below the base is ignored; otherwise it becomes the
// base, keeping the entries above it if it is at or below the commit.
func walSaveSnap(s contents, idx uint64, term uint64) contents {
	if idx < s.baseIdx {
		return s
	}
	ents := make([]entry, 0)
	if idx <= s.hs.commit {
		d := idx - s.baseIdx
		for i := d; i < uint64(len(s.ents)); i++ {
			ents = append(ents, s.ents[i])
		}
	}
	return contents{hs: s.hs, baseIdx: idx, baseTerm: term, ents: ents}
}

// readEnt is ReadAll's step on an entry e: at or below the base, nothing; else at e.index-b-1,
// truncating what follows; past the end, a failure (ErrSliceOutOfRange).
func readEnt(b uint64, ents []entry, e entry) ([]entry, bool) {
	if e.index <= b {
		// an entry at or below the base truncates the log there (ReadAll: ents[:0]; W3 fix of
		// the W1.5 transliteration, which kept the entries; walref.ReadEnt had it right)
		return make([]entry, 0), true
	}
	off := e.index - b - 1
	if off > uint64(len(ents)) {
		return ents, false
	}
	out := make([]entry, 0, off+1)
	for i := uint64(0); i < off; i++ {
		out = append(out, ents[i])
	}
	return append(out, e), true
}

// walFoldChk folds the history, entry by entry through readEnt; false once one fails.
func walFoldChk(h []walOp) (contents, bool) {
	var s contents
	s.ents = make([]entry, 0)
	for i := 0; i < len(h); i++ {
		o := h[i]
		if o.snap {
			s = walSaveSnap(s, o.idx, o.term)
			continue
		}
		s.hs = phsNext(s.hs, o.hs)
		for j := 0; j < len(o.ents); j++ {
			ents, ok := readEnt(s.baseIdx, s.ents, o.ents[j])
			if !ok {
				return s, false
			}
			s.ents = ents
		}
	}
	return s, true
}

// walRead is what a restart reads from the files of a WAL whose history is h: the snapshot
// records above the last saved commit dropped, the rest folded; false when the read fails.
func walRead(h []walOp) (contents, bool) {
	c := walLastHS(h).commit
	f := make([]walOp, 0, len(h))
	for i := 0; i < len(h); i++ {
		if h[i].snap && h[i].idx > c {
			continue
		}
		f = append(f, h[i])
	}
	return walFoldChk(f)
}

// walImgs enumerates walImg h n: the first j operations (n <= j <= len h), then possibly the first
// k entries of operation j when it is a Save (its state record, written last, lost).
func walImgs(h []walOp, n int) [][]walOp {
	out := make([][]walOp, 0)
	for j := n; j <= len(h); j++ {
		out = append(out, copyOps(h[:j]))
		if j < len(h) && !h[j].snap {
			for k := 0; k <= len(h[j].ents); k++ {
				if k == len(h[j].ents) && hsEmpty(h[j].hs) {
					break
				}
				img := copyOps(h[:j])
				img = append(img, walOp{ents: copyEnts(h[j].ents[:k])})
				out = append(out, img)
			}
		}
	}
	return out
}

// walFold is the previous model (walSave/walSaveSnap folded); opResend picks re-sent entries
// from it (any entries are fine for Save).
func walFold(h []walOp) contents {
	var s contents
	s.ents = make([]entry, 0)
	for i := 0; i < len(h); i++ {
		o := h[i]
		if o.snap {
			s = walSaveSnap(s, o.idx, o.term)
			continue
		}
		s.hs = phsNext(s.hs, o.hs)
		s.ents = appendEnts(s.baseIdx, s.ents, o.ents)
	}
	return s
}

// appendEnts is RaftState's appendEnts: the entries at or below the base dropped, the rest
// replacing the log from their first index on.
func appendEnts(b uint64, old []entry, es []entry) []entry {
	start := 0
	for start < len(es) && es[start].index <= b {
		start++
	}
	if start == len(es) {
		return old
	}
	k := es[start].index - b - 1
	if k > uint64(len(old)) {
		k = uint64(len(old))
	}
	out := make([]entry, 0)
	for i := uint64(0); i < k; i++ {
		out = append(out, old[i])
	}
	for i := start; i < len(es); i++ {
		out = append(out, es[i])
	}
	return out
}

// walReadFrom is what a restart reads when the WAL's first files were purged: the records before
// position k (1 <= k) of the history h are gone and the decodable records are its suffix h[k:].
// The snapshot records of the suffix above the history's last saved commit are dropped, the newest
// remaining one opened at, and the rest folded from it (ReadAll skips the entries at or below the
// opened snapshot), starting from the purged prefix's last hard state. W4 Draft §1.3's correction
// (decision 3): the first kept file's header repeats the hard state saved before it (cut's
// saveState), so the fold starts from walLastHS(h[:k]), and the commit that drops the snapshot
// records is the whole history's (W1.5's version used the suffix's own: zero when it has no
// state record). False if no snapshot record remains, or the fold fails.
func walReadFrom(h []walOp, k int) (contents, bool) {
	s := h[k:]
	c := walLastHS(h).commit
	found := false
	var base contents
	base.ents = make([]entry, 0)
	base.hs = walLastHS(h[:k])
	f := make([]walOp, 0, len(s))
	for i := 0; i < len(s); i++ {
		if s[i].snap && s[i].idx > c {
			continue
		}
		if s[i].snap && (!found || s[i].idx >= base.baseIdx) {
			found = true
			base.baseIdx = s[i].idx
			base.baseTerm = s[i].term
		}
		f = append(f, s[i])
	}
	if !found {
		return base, false
	}
	st := base
	for i := 0; i < len(f); i++ {
		o := f[i]
		if o.snap {
			st = walSaveSnap(st, o.idx, o.term)
			continue
		}
		st.hs = phsNext(st.hs, o.hs)
		for j := 0; j < len(o.ents); j++ {
			ents, ok := readEnt(st.baseIdx, st.ents, o.ents[j])
			if !ok {
				return st, false
			}
			st.ents = ents
		}
	}
	return st, true
}

// walReadCut is the spec's relaxed reader (WalHist.lean): the whole history (k = 0), or the read
// from a purged prefix k.
func walReadCut(h []walOp, k uint64) (contents, bool) {
	if k == 0 {
		return walRead(h)
	}
	return walReadFrom(h, int(k))
}

// lastIdx is walLastIdx (WalDisk.lean): the larger of the last entry record's index and the
// highest snapshot record's index of h (0 if none).
func lastIdx(h []walOp) uint64 {
	var e uint64
	var sn uint64
	for i := 0; i < len(h); i++ {
		if h[i].snap {
			if h[i].idx > sn {
				sn = h[i].idx
			}
		} else if len(h[i].ents) > 0 {
			e = h[i].ents[len(h[i].ents)-1].index
		}
	}
	if sn > e {
		return sn
	}
	return e
}

// cutPos is walCutPos (WalDisk.lean): a WAL file can start at position b of h (0, or right after
// a Save that writes a record).
func cutPos(h []walOp, b int) bool {
	if b == 0 {
		return true
	}
	o := h[b-1]
	return !o.snap && !(hsEmpty(o.hs) && len(o.ents) == 0)
}

// nameBound is walNameBound h a false (WalDisk.lean), for histories with no index 2^64-1: the
// last position b at which a file named at most a can start (walLastIdx of the prefix plus one at
// most a); Open at a unlocks only records before it, and ReleaseLockTo(a) too (walOpenPos,
// walReleasePos <= it).
func nameBound(h []walOp, a uint64) uint64 {
	var best uint64
	for b := 0; b <= len(h); b++ {
		if cutPos(h, b) && lastIdx(h[:b])+1 <= a {
			best = uint64(b)
		}
	}
	return best
}

// openBound is the largest nameBound at a of the images imgs (an Open at a after a crash unlocks
// below nameBound of the image it opened, one of them).
func openBound(imgs [][]walOp, a uint64) uint64 {
	var best uint64
	for i := 0; i < len(imgs); i++ {
		b := nameBound(imgs[i], a)
		if b > best {
			best = b
		}
	}
	return best
}
