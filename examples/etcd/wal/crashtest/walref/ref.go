// Package walref is a Go transliteration of the Scope's pure WAL vocabulary (scope.md §2.1:
// walFold, walSave, walSaveSnap, walLastHS, walMustSync, readEnt, walFoldChk, walRead, walImg),
// over a record-level view of a WAL history, and the restart read path of etcd's bootstrap.
package walref

import (
	"fmt"
	"strings"
)

// HS is a hard state.
type HS struct{ Term, Vote, Commit uint64 }

// Empty is raft.IsEmptyHardState.
func (h HS) Empty() bool { return h == HS{} }

// Ent is an entry (Data is compared as bytes).
type Ent struct {
	Index, Term uint64
	Data        string
}

// Op is one WAL operation: Save(HS, Ents) or SaveSnapshot(Index, Term).
type Op struct {
	Snap      bool
	HS        HS
	Ents      []Ent
	Idx, Term uint64
}

func (o Op) String() string {
	if o.Snap {
		return fmt.Sprintf("snap(%d,%d)", o.Idx, o.Term)
	}
	var b strings.Builder
	fmt.Fprintf(&b, "save(hs=%d/%d/%d,", o.HS.Term, o.HS.Vote, o.HS.Commit)
	if len(o.Ents) > 0 {
		fmt.Fprintf(&b, "e%d..%d@t%d", o.Ents[0].Index, o.Ents[len(o.Ents)-1].Index, o.Ents[len(o.Ents)-1].Term)
	}
	b.WriteString(")")
	return b.String()
}

// Contents is StorContents (the snapshot field kept as its index and term, or absent).
type Contents struct {
	HS                HS
	HasSnap           bool
	BaseIdx, BaseTerm uint64
	Ents              []Ent
}

// Key is what a restart's result is compared on: the base, the hard state, the entries (the
// snapshot field is not returned by ReadAll).
func (c Contents) Key() string {
	var b strings.Builder
	fmt.Fprintf(&b, "base=%d/%d hs=%d/%d/%d ents=[", c.BaseIdx, c.BaseTerm, c.HS.Term, c.HS.Vote, c.HS.Commit)
	for i, e := range c.Ents {
		if i > 0 {
			b.WriteString(" ")
		}
		fmt.Fprintf(&b, "%d@%d:%x", e.Index, e.Term, hash(e.Data))
	}
	b.WriteString("]")
	return b.String()
}

func hash(s string) uint32 {
	var h uint32 = 2166136261
	for i := 0; i < len(s); i++ {
		h ^= uint32(s[i])
		h *= 16777619
	}
	return h
}

// WalFresh is walFresh.
func WalFresh() Contents { return Contents{} }

func phsNext(p, h HS) HS {
	if h.Empty() {
		return p
	}
	return h
}

// appendEnts is RaftState's appendEnts b es(old) ents(new).
func appendEnts(b uint64, old, ents []Ent) []Ent {
	if len(ents) == 0 {
		return old
	}
	e0 := ents[0].Index
	drop := int64(b) + 1 - int64(e0)
	if drop > 0 {
		if drop > int64(len(ents)) {
			ents = nil
		} else {
			ents = ents[drop:]
		}
	}
	// plogTruncateAppend b old ents
	if len(ents) == 0 {
		return old
	}
	k := int64(ents[0].Index) - int64(b) - 1
	if k < 0 {
		k = 0
	}
	if k > int64(len(old)) {
		k = int64(len(old))
	}
	out := append([]Ent{}, old[:k]...)
	return append(out, ents...)
}

// WalSave is walSave.
func WalSave(s Contents, h HS, es []Ent) Contents {
	s.HS = phsNext(s.HS, h)
	s.Ents = appendEnts(s.BaseIdx, s.Ents, es)
	return s
}

// WalSaveSnap is walSaveSnap.
func WalSaveSnap(s Contents, idx, term uint64) Contents {
	if idx < s.BaseIdx {
		return s
	}
	var ents []Ent
	if idx <= s.HS.Commit {
		d := idx - s.BaseIdx
		if d < uint64(len(s.Ents)) {
			ents = append([]Ent{}, s.Ents[d:]...)
		}
	}
	s.BaseIdx, s.BaseTerm, s.HasSnap, s.Ents = idx, term, true, ents
	return s
}

// WalFold is walFold.
func WalFold(H []Op) Contents {
	s := WalFresh()
	for _, o := range H {
		if o.Snap {
			s = WalSaveSnap(s, o.Idx, o.Term)
		} else {
			s = WalSave(s, o.HS, o.Ents)
		}
	}
	return s
}

// WalLastHS is walLastHS.
func WalLastHS(H []Op) HS {
	var p HS
	for _, o := range H {
		if !o.Snap {
			p = phsNext(p, o.HS)
		}
	}
	return p
}

// WalMustSync is walMustSync.
func WalMustSync(H []Op, h HS, es []Ent) bool {
	l := WalLastHS(H)
	return len(es) > 0 || (!h.Empty() && (h.Vote != l.Vote || h.Term != l.Term))
}

// ReadEnt is readEnt.
func ReadEnt(b uint64, ents []Ent, e Ent) ([]Ent, bool) {
	if e.Index <= b {
		return nil, true
	}
	off := e.Index - b - 1
	if off > uint64(len(ents)) {
		return nil, false
	}
	out := append([]Ent{}, ents[:off]...)
	return append(out, e), true
}

// WalFoldChk is walFoldChk.
func WalFoldChk(H []Op) (Contents, bool) {
	s := WalFresh()
	for _, o := range H {
		if o.Snap {
			s = WalSaveSnap(s, o.Idx, o.Term)
			continue
		}
		s.HS = phsNext(s.HS, o.HS)
		for _, e := range o.Ents {
			var ok bool
			if s.Ents, ok = ReadEnt(s.BaseIdx, s.Ents, e); !ok {
				return s, false
			}
		}
	}
	return s, true
}

// WalRead is walRead: the snapshot records above the last saved commit dropped, then walFoldChk.
func WalRead(I []Op) (Contents, bool) {
	c := WalLastHS(I).Commit
	var f []Op
	for _, o := range I {
		if o.Snap && o.Idx > c {
			continue
		}
		f = append(f, o)
	}
	return WalFoldChk(f)
}

// WalImgs enumerates walImg H n: the first j ops (n <= j <= |H|), then possibly the first k
// entries of op j when it is a Save (its state lost).
func WalImgs(H []Op, n int) [][]Op {
	var out [][]Op
	for j := n; j <= len(H); j++ {
		out = append(out, H[:j:j])
		if j < len(H) && !H[j].Snap {
			for k := 0; k <= len(H[j].Ents); k++ {
				if k == len(H[j].Ents) && H[j].HS.Empty() {
					break // = H[:j+1]
				}
				I := append(append([]Op{}, H[:j]...), Op{Ents: H[j].Ents[:k:k]})
				out = append(out, I)
			}
		}
	}
	return out
}

// Rec is one record of the history, at record level (CRC and metadata records omitted).
type Rec struct {
	Kind byte // 'e' entry, 's' state, 'n' snapshot
	E    Ent
	HS   HS
	Idx  uint64
	Term uint64
}

func (r Rec) Eq(o Rec) bool {
	return r.Kind == o.Kind && r.E == o.E && r.HS == o.HS && r.Idx == o.Idx && r.Term == o.Term
}

func (r Rec) String() string {
	switch r.Kind {
	case 'e':
		return fmt.Sprintf("e%d@%d", r.E.Index, r.E.Term)
	case 's':
		return fmt.Sprintf("hs%d/%d/%d", r.HS.Term, r.HS.Vote, r.HS.Commit)
	}
	return fmt.Sprintf("snap%d@%d", r.Idx, r.Term)
}

// Flatten is the records a history writes (Save: its entries, then its state unless empty).
// bounds[i] is the record position where op i starts; bounds[len(H)] the end.
func Flatten(H []Op) (recs []Rec, bounds []int) {
	for _, o := range H {
		bounds = append(bounds, len(recs))
		if o.Snap {
			recs = append(recs, Rec{Kind: 'n', Idx: o.Idx, Term: o.Term})
			continue
		}
		for _, e := range o.Ents {
			recs = append(recs, Rec{Kind: 'e', E: e})
		}
		if !o.HS.Empty() {
			recs = append(recs, Rec{Kind: 's', HS: o.HS})
		}
	}
	bounds = append(bounds, len(recs))
	return
}

// Group turns a record sequence back into ops (a Save: entries then an optional state).
func Group(recs []Rec) []Op {
	var out []Op
	var cur *Op
	for _, r := range recs {
		switch r.Kind {
		case 'n':
			if cur != nil {
				out = append(out, *cur)
				cur = nil
			}
			out = append(out, Op{Snap: true, Idx: r.Idx, Term: r.Term})
		case 'e':
			if cur == nil {
				cur = &Op{}
			}
			cur.Ents = append(cur.Ents, r.E)
		case 's':
			if cur == nil {
				cur = &Op{}
			}
			cur.HS = r.HS
			out = append(out, *cur)
			cur = nil
		}
	}
	if cur != nil {
		out = append(out, *cur)
	}
	return out
}

// ImgRecOK says whether the record sequence I (from position `from` of the history's records, the
// records before it purged) is a walImg H n image at record level, and why not.
func ImgRecOK(H []Op, n int, I []Rec, purged bool) (bool, string) {
	recs, bounds := Flatten(H)
	starts := []int{0}
	if purged {
		starts = nil
		for a := 0; a <= len(recs); a++ {
			if len(I) == 0 || (a < len(recs) && recs[a].Eq(I[0])) {
				starts = append(starts, a)
			}
		}
	}
	why := ""
	for _, a := range starts {
		m := a
		ok := true
		for i, r := range I {
			if a+i >= len(recs) || !recs[a+i].Eq(r) {
				ok = false
				if a+i >= len(recs) {
					why = fmt.Sprintf("record %d (%v) beyond the history's %d records", i, r, len(recs))
				} else {
					why = fmt.Sprintf("record %d is %v, the history's is %v", i, r, recs[a+i])
				}
				break
			}
			m = a + i + 1
		}
		if !ok {
			continue
		}
		// m must be an allowed cut: an op boundary j >= n, or inside save j >= n before its state
		for j := n; j <= len(H); j++ {
			if m == bounds[j] {
				return true, ""
			}
			if j < len(H) && !H[j].Snap && m > bounds[j] && m <= bounds[j]+len(H[j].Ents) {
				return true, ""
			}
		}
		why = fmt.Sprintf("cut at record %d (synced ops %d end at record %d)", m, n, bounds[n])
	}
	return false, why
}
