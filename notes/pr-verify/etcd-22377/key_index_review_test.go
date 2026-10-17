package mvcc

import (
	"fmt"
	"reflect"
	"testing"

	"go.uber.org/zap"
)

// Review of etcd-io/etcd#22377: exhaustive single-key histories (puts and
// deletes, several per main revision), every compaction revision.

type rvOp struct {
	rev  Revision
	tomb bool
}

func enumHistories(maxMain int64, maxPerMain, maxLen int) [][]rvOp {
	var out [][]rvOp
	var rec func(h []rvOp, main int64, sub int64, alive bool)
	rec = func(h []rvOp, main int64, sub int64, alive bool) {
		if len(h) > 0 && h[0].tomb == false {
			cp := append([]rvOp(nil), h...)
			out = append(out, cp)
		}
		if len(h) >= maxLen {
			return
		}
		// next op: same main (if sub < maxPerMain) or a later main
		for m := main; m <= maxMain; m++ {
			s := int64(0)
			if m == main {
				s = sub
			}
			if s >= int64(maxPerMain) {
				continue
			}
			r := Revision{Main: m, Sub: s}
			rec(append(h, rvOp{r, false}), m, s+1, true)
			if alive {
				rec(append(h, rvOp{r, true}), m, s+1, false)
			}
		}
	}
	rec(nil, 1, 0, false)
	return out
}

func buildKI(lg *zap.Logger, h []rvOp) *keyIndex {
	ki := &keyIndex{key: []byte("k")}
	for _, o := range h {
		if o.tomb {
			if err := ki.tombstone(lg, o.rev.Main, o.rev.Sub); err != nil {
				panic(err)
			}
		} else {
			ki.put(lg, o.rev.Main, o.rev.Sub)
		}
	}
	return ki
}

// the doCompact of pre-#18274 (tomb > atRev) and of current main (tomb >= atRev)
func doCompactVariant(ki *keyIndex, atRev int64, available map[Revision]struct{}, inclusive bool) (int, int) {
	f := func(rev Revision) bool {
		if rev.Main <= atRev {
			available[rev] = struct{}{}
			return false
		}
		return true
	}
	genIdx, g := 0, &ki.generations[0]
	for genIdx < len(ki.generations)-1 {
		tomb := g.revs[len(g.revs)-1].Main
		if tomb > atRev || (inclusive && tomb == atRev) {
			break
		}
		genIdx++
		g = &ki.generations[genIdx]
	}
	return genIdx, g.walk(f)
}

func keepVariant(ki *keyIndex, atRev int64, inclusive bool) map[Revision]struct{} {
	av := map[Revision]struct{}{}
	genIdx, revIndex := doCompactVariant(ki, atRev, av, inclusive)
	g := &ki.generations[genIdx]
	if !g.isEmpty() && revIndex == len(g.revs)-1 && genIdx != len(ki.generations)-1 {
		delete(av, g.revs[revIndex])
	}
	return av
}

type getRes struct {
	mod     Revision
	crMain  int64
	ver     int64
	found   bool
}

func getAt(lg *zap.Logger, ki *keyIndex, r int64, crMainOnly bool) getRes {
	if ki.isEmpty() {
		return getRes{}
	}
	m, c, v, err := ki.get(lg, r)
	if err != nil {
		return getRes{}
	}
	return getRes{m, c.Main, v, true}
}

// restore the index from a backend holding rows `rows` (in revision order),
// as restoreIntoIndex does; meta gives each put row's CreateRevision and Version.
func restoreKI(lg *zap.Logger, rows []rvOp, meta map[Revision][2]int64) *keyIndex {
	var ki *keyIndex
	for _, o := range rows {
		if ki != nil {
			if o.tomb {
				_ = ki.tombstone(lg, o.rev.Main, o.rev.Sub)
				continue
			}
			ki.put(lg, o.rev.Main, o.rev.Sub)
		} else {
			ki = &keyIndex{key: []byte("k")}
			if o.tomb {
				ki.restoreTombstone(lg, o.rev.Main, o.rev.Sub)
			} else {
				ki.restore(lg, Revision{Main: meta[o.rev][0]}, o.rev, meta[o.rev][1])
			}
		}
	}
	return ki
}

func histStr(h []rvOp) string {
	s := ""
	for _, o := range h {
		if o.tomb {
			s += fmt.Sprintf(" %d.%dT", o.rev.Main, o.rev.Sub)
		} else {
			s += fmt.Sprintf(" %d.%d", o.rev.Main, o.rev.Sub)
		}
	}
	return s
}

func TestReviewCompactRecreate(t *testing.T) {
	lg := zap.NewNop()
	const maxMain = 4
	hs := enumHistories(maxMain, 3, 6)
	cases, keepDiffPre, keepDiffMain, availDiffMain, availDiffPre := 0, 0, 0, 0, 0
	fails := 0
	report := func(format string, a ...any) {
		fails++
		if fails < 30 {
			t.Errorf(format, a...)
		}
	}
	for _, h := range hs {
		// per-row CreateRevision and Version, as the store writes them
		meta := map[Revision][2]int64{}
		var cr, ver int64
		for _, o := range h {
			if o.tomb {
				cr, ver = 0, 0
				continue
			}
			if ver == 0 {
				cr = o.rev.Main
			}
			ver++
			meta[o.rev] = [2]int64{cr, ver}
		}
		for atRev := int64(0); atRev <= maxMain+1; atRev++ {
			cases++
			orig := buildKI(lg, h)

			// keep() vs pre-#18274 and main
			kp := map[Revision]struct{}{}
			orig.keep(atRev, kp)
			if !reflect.DeepEqual(kp, keepVariant(buildKI(lg, h), atRev, false)) {
				keepDiffPre++
				report("keep differs from pre-#18274: %s at %d: %v vs %v", histStr(h), atRev, kp, keepVariant(buildKI(lg, h), atRev, false))
			}
			if !reflect.DeepEqual(kp, keepVariant(buildKI(lg, h), atRev, true)) {
				keepDiffMain++
			}

			ki := buildKI(lg, h)
			av := map[Revision]struct{}{}
			ki.compact(lg, atRev, av)
			avMain := map[Revision]struct{}{}
			doCompactVariant(buildKI(lg, h), atRev, avMain, true)
			avPre := map[Revision]struct{}{}
			doCompactVariant(buildKI(lg, h), atRev, avPre, false)
			if !reflect.DeepEqual(av, avMain) {
				availDiffMain++
			}
			if !reflect.DeepEqual(av, avPre) {
				availDiffPre++
				for r := range av {
					if _, ok := avPre[r]; !ok && r.Main != atRev {
						report("avail change not at atRev: %s at %d", histStr(h), atRev)
					}
				}
				for r := range avPre {
					if _, ok := av[r]; !ok && r.Main != atRev {
						report("avail change not at atRev: %s at %d", histStr(h), atRev)
					}
				}
			}
			if len(av) > 1 {
				report("more than one available: %s at %d: %v", histStr(h), atRev, av)
			}

			// (#18274) the last word at atRev, a tombstone at atRev, is kept
			var last *rvOp
			for i := range h {
				if h[i].rev.Main <= atRev {
					last = &h[i]
				}
			}
			if last != nil && last.tomb && last.rev.Main == atRev {
				if _, ok := av[last.rev]; !ok {
					report("final tombstone at atRev not kept: %s at %d: %v", histStr(h), atRev, av)
				}
			}
			// what is kept is the last word at atRev (if any revision <= atRev), or nothing
			// when the last word is a tombstone below atRev
			if last != nil {
				want := map[Revision]struct{}{last.rev: {}}
				if last.tomb && last.rev.Main < atRev {
					want = map[Revision]struct{}{}
				}
				if !reflect.DeepEqual(av, want) {
					report("available is not the last word: %s at %d: %v want %v", histStr(h), atRev, av, want)
				}
			}

			// rows left in the backend
			var rows []rvOp
			for _, o := range h {
				if o.rev.Main > atRev {
					rows = append(rows, o)
				} else if _, ok := av[o.rev]; ok {
					rows = append(rows, o)
				}
			}
			var rk *keyIndex
			if len(rows) > 0 {
				rk = restoreKI(lg, rows, meta)
			}
			for r := atRev; r <= maxMain+1; r++ {
				want := getAt(lg, orig, r, false)
				got := getAt(lg, ki, r, false)
				if want != got {
					report("compacted index read differs: %s at %d, read %d: %v vs %v", histStr(h), atRev, r, got, want)
				}
				if want.found {
					// the row must be in the backend
					okRow := false
					for _, o := range rows {
						if o.rev == want.mod {
							okRow = true
						}
					}
					if !okRow {
						report("read names a deleted row: %s at %d, read %d: %v", histStr(h), atRev, r, want.mod)
					}
				}
				var rg getRes
				if rk != nil {
					rg = getAt(lg, rk, r, true)
				}
				if rg != want {
					report("restored index read differs: %s at %d, read %d: %v vs %v", histStr(h), atRev, r, rg, want)
				}
			}
			// a second compaction composes
			for c2 := atRev + 1; c2 <= maxMain+1; c2++ {
				k1 := buildKI(lg, h)
				a1 := map[Revision]struct{}{}
				k1.compact(lg, atRev, map[Revision]struct{}{})
				k2 := buildKI(lg, h)
				a2 := map[Revision]struct{}{}
				k2.compact(lg, c2, a2)
				if k1.isEmpty() {
					// treeIndex drops an empty key index
					if len(a2) != 0 || !k2.isEmpty() {
						report("dropped key index revives: %s at %d then %d", histStr(h), atRev, c2)
					}
					continue
				}
				k1.compact(lg, c2, a1)
				if !reflect.DeepEqual(a1, a2) || !k1.equal(k2) {
					report("compactions do not compose: %s at %d then %d", histStr(h), atRev, c2)
				}
			}
		}
	}
	t.Logf("histories %d, cases %d; keep diffs vs pre-#18274 %d, vs main %d; available diffs vs pre %d, vs main %d; failures %d",
		len(hs), cases, keepDiffPre, keepDiffMain, availDiffPre, availDiffMain, fails)
}
