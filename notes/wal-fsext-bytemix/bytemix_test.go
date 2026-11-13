// Copyright 2026 The etcd Authors
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

package wal

// Byte-mix power-loss images of the WAL's unsynced tail.
//
// A power loss may leave each byte written since the last fdatasync either at its old value or at
// its new one, independently. This test builds WALs with real Create/Save/SaveSnapshot calls, takes
// the frames of the last k records (k = 1..3) as the unsynced tail, and enumerates mixes of their
// bytes with the old ones: zeros (the preallocated or zeroed tail, as after ReadAll's ZeroToEnd and
// its fdatasync), or stale bytes of another record sequence at the same offsets or shifted (as when
// the zeroing is lost, upstream, or after a reused N.tmp). Exhaustive over the bytes of each frame
// that are not inside Record.Data (length word, tags, Type, Crc, Data's length, padding), random over
// the whole tail. Each image goes through the restart bootstrap does: ValidSnapshotEntries, Open at
// the newest valid snapshot, ReadAll, on io.ErrUnexpectedEOF Repair and ReadAll again.
//
// Fast path: the real decoder and the real ReadAll (read mode, which accepts io.EOF and
// io.ErrUnexpectedEOF: the outcome of Repair-then-ReadAll in write mode) over an in-memory image;
// ValidSnapshotEntries' loop copied. A sample, and every image classified "wrong", is re-run on real
// files with the real Open/ReadAll/Repair/ValidSnapshotEntries.

import (
	"bytes"
	"errors"
	"fmt"
	"io"
	"io/fs"
	"math/rand"
	"os"
	"path/filepath"
	"sort"
	"strings"
	"sync"
	"testing"
	"time"

	"go.uber.org/zap"
	"google.golang.org/protobuf/proto"

	"go.etcd.io/etcd/pkg/v3/pbutil"
	"go.etcd.io/etcd/server/v3/storage/wal/walpb"
	"go.etcd.io/raft/v3/raftpb"
)

// ---- in-memory file ----

type bmInfo struct {
	name string
	size int64
}

func (i bmInfo) Name() string       { return i.name }
func (i bmInfo) Size() int64        { return i.size }
func (i bmInfo) Mode() fs.FileMode  { return 0o600 }
func (i bmInfo) ModTime() time.Time { return time.Time{} }
func (i bmInfo) IsDir() bool        { return false }
func (i bmInfo) Sys() any           { return nil }

type bmFile struct {
	b    []byte // the image's first len(b) bytes; zeros after, up to size
	off  int64
	size int64
}

func (m *bmFile) Read(p []byte) (int, error) {
	if m.off >= m.size {
		return 0, io.EOF
	}
	n := int64(len(p))
	if rem := m.size - m.off; n > rem {
		n = rem
	}
	c := 0
	if m.off < int64(len(m.b)) {
		c = copy(p[:n], m.b[m.off:])
	}
	for i := int64(c); i < n; i++ {
		p[i] = 0
	}
	m.off += n
	return int(n), nil
}

func (m *bmFile) FileInfo() (fs.FileInfo, error) {
	return bmInfo{"0000000000000000-0000000000000000.wal", m.size}, nil
}

// ---- WAL generation ----

type bmOp struct {
	hs   *raftpb.HardState
	ents []*raftpb.Entry
	snap *walpb.Snapshot
}

func bmEnt(idx, term uint64, typ int, n int, r *rand.Rand) *raftpb.Entry {
	e := &raftpb.Entry{Index: new(idx), Term: new(term)}
	switch typ {
	case 1:
		e.Type = new(raftpb.EntryNormal)
	case 2:
		e.Type = new(raftpb.EntryConfChange)
	}
	if n >= 0 {
		d := make([]byte, n)
		r.Read(d)
		e.Data = d
	}
	return e
}

func bmHS(term, vote, commit uint64) *raftpb.HardState {
	return &raftpb.HardState{Term: new(term), Vote: new(vote), Commit: new(commit)}
}

func bmSnap(idx, term uint64) *walpb.Snapshot {
	return &walpb.Snapshot{Index: new(idx), Term: new(term), ConfState: &raftpb.ConfState{Voters: []uint64{1, 2, 3}}}
}

// bmWrite writes a WAL with the ops (after Create) and returns its single segment's bytes and size.
func bmWrite(t testing.TB, ops []bmOp) ([]byte, int64) {
	tmp, err := os.MkdirTemp("", "bytemix-gen")
	if err != nil {
		t.Fatal(err)
	}
	defer os.RemoveAll(tmp)
	dir := filepath.Join(tmp, "wal")
	w, err := Create(zap.NewNop(), dir, []byte("metadata"))
	if err != nil {
		t.Fatal(err)
	}
	for _, op := range ops {
		if op.snap != nil {
			if err := w.SaveSnapshot(op.snap); err != nil {
				t.Fatal(err)
			}
			continue
		}
		if err := w.Save(op.hs, op.ents); err != nil {
			t.Fatal(err)
		}
	}
	if len(w.locks) != 1 {
		t.Fatalf("expected one segment, got %d", len(w.locks))
	}
	name := filepath.Join(dir, filepath.Base(w.tail().Name()))
	w.Close()
	b, err := os.ReadFile(name)
	if err != nil {
		t.Fatal(err)
	}
	size := int64(len(b))
	end := len(b)
	for end > 0 && b[end-1] == 0 {
		end--
	}
	return b[:(end+7)/8*8], size
}

type bmRec struct {
	typ  int64
	crc  uint32
	data []byte
}

func (r bmRec) eq(o bmRec) bool {
	return r.typ == o.typ && r.crc == o.crc && bytes.Equal(r.data, o.data)
}

// bmFrames decodes the image and returns the records and the end offset of each frame.
func bmFrames(t testing.TB, b []byte, size int64) ([]bmRec, []int64) {
	recs, ends, err := bmDecode(b, size)
	if !errors.Is(err, io.EOF) {
		t.Fatalf("written WAL does not decode: %v", err)
	}
	return recs, ends
}

func bmDecode(b []byte, size int64) (recs []bmRec, ends []int64, err error) {
	d := NewDecoder(&bmFile{b: b, size: size})
	rec := &walpb.Record{}
	for err = d.Decode(rec); err == nil; err = d.Decode(rec) {
		recs = append(recs, bmRec{rec.GetType(), rec.GetCrc(), append([]byte(nil), rec.Data...)})
		ends = append(ends, d.LastOffset())
		if rec.GetType() == CrcType {
			d.UpdateCRC(rec.GetCrc())
		}
	}
	return
}

// ---- the restart, in memory ----

type bmOutcome struct {
	kind   string // "ok", "fatal", "panic"
	why    string
	md     []byte
	hs     *raftpb.HardState
	ents   []*raftpb.Entry
	snaps  []*walpb.Snapshot
	start  *walpb.Snapshot
	recs   []bmRec
	stopOK bool // the decoder stopped at io.EOF or io.ErrUnexpectedEOF
}

func (o bmOutcome) key() string {
	if o.kind != "ok" {
		return o.kind
	}
	var sb strings.Builder
	fmt.Fprintf(&sb, "md=%x hs=%v start=%v snaps=", o.md, o.hs.String(), o.start.String())
	for _, s := range o.snaps {
		sb.WriteString(s.String() + ";")
	}
	sb.WriteString(" ents=")
	for _, e := range o.ents {
		b, _ := proto.Marshal(e)
		fmt.Fprintf(&sb, "%x;", b)
	}
	return sb.String()
}

// bmVSE is validSnapshotEntries' loop (wal.go) over the in-memory image.
func bmVSE(b []byte, size int64) ([]*walpb.Snapshot, error) {
	var snaps []*walpb.Snapshot
	state := &raftpb.HardState{}
	var err error
	rec := &walpb.Record{}
	decoder := NewDecoder(&bmFile{b: b, size: size})
	for err = decoder.Decode(rec); err == nil; err = decoder.Decode(rec) {
		switch rec.GetType() {
		case SnapshotType:
			loadedSnap := &walpb.Snapshot{}
			pbutil.MustUnmarshalMessage(loadedSnap, rec.Data)
			snaps = append(snaps, loadedSnap)
		case StateType:
			state = MustUnmarshalState(rec.Data)
		case CrcType:
			crc := decoder.LastCRC()
			if crc != 0 && rec.Validate(crc) != nil {
				return nil, ErrCRCMismatch
			}
			decoder.UpdateCRC(rec.GetCrc())
		}
	}
	if !errors.Is(err, io.EOF) && !errors.Is(err, io.ErrUnexpectedEOF) {
		return nil, err
	}
	n := 0
	for _, s := range snaps {
		if s.GetIndex() <= state.GetCommit() {
			snaps[n] = s
			n++
		}
	}
	return snaps[:n:n], nil
}

func bmRestartMem(b []byte, size int64) (o bmOutcome) {
	defer func() {
		if r := recover(); r != nil {
			o.kind, o.why = "panic", fmt.Sprint(r)
		}
	}()
	recs, _, derr := bmDecode(b, size)
	o.recs = recs
	o.stopOK = errors.Is(derr, io.EOF) || errors.Is(derr, io.ErrUnexpectedEOF)
	snaps, err := bmVSE(b, size)
	if err != nil {
		return bmOutcome{kind: "fatal", why: "vse: " + err.Error(), recs: recs, stopOK: o.stopOK}
	}
	start := &walpb.Snapshot{}
	if len(snaps) > 0 {
		start = snaps[len(snaps)-1]
	}
	w := &WAL{lg: zap.NewNop(), start: start.Clone(), decoder: NewDecoder(&bmFile{b: b, size: size})}
	md, hs, ents, err := w.ReadAll()
	if err != nil {
		return bmOutcome{kind: "fatal", why: "readall: " + err.Error(), recs: recs, stopOK: o.stopOK}
	}
	return bmOutcome{kind: "ok", md: md, hs: hs, ents: ents, snaps: snaps, start: start, recs: recs, stopOK: o.stopOK}
}

// ---- the restart, on real files ----

func bmRestartReal(t testing.TB, b []byte, size int64) (o bmOutcome) {
	defer func() {
		if r := recover(); r != nil {
			o.kind, o.why = "panic", fmt.Sprint(r)
		}
	}()
	tmp, err := os.MkdirTemp("", "bytemix-img")
	if err != nil {
		t.Fatal(err)
	}
	defer os.RemoveAll(tmp)
	dir := filepath.Join(tmp, "wal")
	if err := os.MkdirAll(dir, 0o700); err != nil {
		t.Fatal(err)
	}
	img := make([]byte, size)
	copy(img, b)
	if err := os.WriteFile(filepath.Join(dir, walName(0, 0)), img, 0o600); err != nil {
		t.Fatal(err)
	}
	lg := zap.NewNop()
	snaps, err := ValidSnapshotEntries(lg, dir)
	if err != nil {
		return bmOutcome{kind: "fatal", why: "vse: " + err.Error()}
	}
	start := &walpb.Snapshot{}
	if len(snaps) > 0 {
		start = snaps[len(snaps)-1]
	}
	repaired := false
	for {
		w, err := Open(lg, dir, start)
		if err != nil {
			return bmOutcome{kind: "fatal", why: "open: " + err.Error()}
		}
		md, hs, ents, err := w.ReadAll()
		w.Close()
		if err != nil {
			if repaired || !errors.Is(err, io.ErrUnexpectedEOF) {
				return bmOutcome{kind: "fatal", why: "readall: " + err.Error()}
			}
			if !Repair(lg, dir) {
				return bmOutcome{kind: "fatal", why: "repair failed"}
			}
			repaired = true
			continue
		}
		return bmOutcome{kind: "ok", md: md, hs: hs, ents: ents, snaps: snaps, start: start}
	}
}

// ---- scenarios ----

type bmScenario struct {
	name  string
	ops   []bmOp // the whole sequence
	stale []bmOp // another sequence with the same synced prefix, for stale old bytes
}

func bmScenarios() []bmScenario {
	r := rand.New(rand.NewSource(1))
	prefix := func() []bmOp {
		return []bmOp{
			{hs: bmHS(1, 1, 0), ents: []*raftpb.Entry{bmEnt(1, 1, 0, 10, r), bmEnt(2, 1, 1, 40, r)}},
			{hs: bmHS(1, 1, 2)},
		}
	}
	// cont is the continuation after prefix: (index of next entry 3, term 1/2).
	var out []bmScenario
	add := func(name string, tail, stale []bmOp) {
		p := prefix()
		out = append(out, bmScenario{name: name, ops: append(append([]bmOp{}, p...), tail...), stale: append(append([]bmOp{}, p...), stale...)})
	}
	sizes := []int{-1, 0, 3, 60, 117, 120, 300, 700}
	for _, n := range sizes {
		for typ := 0; typ < 3; typ++ {
			add(fmt.Sprintf("entry-n%d-t%d", n, typ),
				[]bmOp{{hs: bmHS(1, 1, 2), ents: []*raftpb.Entry{bmEnt(3, 1, typ, n, r)}}},
				[]bmOp{{hs: bmHS(2, 3, 2)}, {hs: bmHS(2, 3, 2), ents: []*raftpb.Entry{bmEnt(3, 2, 0, 200, r), bmEnt(4, 2, 0, 200, r)}}})
		}
	}
	add("entries3+state",
		[]bmOp{{hs: bmHS(2, 2, 3), ents: []*raftpb.Entry{bmEnt(3, 2, 0, 5, r), bmEnt(4, 2, 1, 130, r), bmEnt(5, 2, 0, 2, r)}}},
		[]bmOp{{hs: bmHS(1, 1, 2), ents: []*raftpb.Entry{bmEnt(3, 1, 0, 5, r), bmEnt(4, 1, 1, 130, r), bmEnt(5, 1, 0, 2, r)}}})
	add("state-only",
		[]bmOp{{hs: bmHS(1, 1, 2), ents: []*raftpb.Entry{bmEnt(3, 1, 0, 20, r)}}, {hs: bmHS(1, 1, 3)}, {hs: bmHS(1, 1, 3), ents: []*raftpb.Entry{bmEnt(4, 1, 0, 8, r)}}},
		[]bmOp{{hs: bmHS(5, 0, 2), ents: []*raftpb.Entry{bmEnt(3, 5, 0, 20, r), bmEnt(4, 5, 0, 20, r)}}})
	add("snapshot",
		[]bmOp{{hs: bmHS(1, 1, 2), ents: []*raftpb.Entry{bmEnt(3, 1, 0, 30, r)}}, {hs: bmHS(1, 1, 3)}, {snap: bmSnap(3, 1)}},
		[]bmOp{{hs: bmHS(1, 1, 2), ents: []*raftpb.Entry{bmEnt(3, 1, 0, 30, r)}}, {hs: bmHS(1, 1, 3)}, {snap: bmSnap(2, 1)}, {hs: bmHS(1, 1, 3), ents: []*raftpb.Entry{bmEnt(4, 1, 0, 9, r)}}})
	add("snapshot-then-entries",
		[]bmOp{{snap: bmSnap(2, 1)}, {hs: bmHS(1, 1, 2), ents: []*raftpb.Entry{bmEnt(3, 1, 0, 5, r), bmEnt(4, 1, 0, 60, r)}}},
		[]bmOp{{hs: bmHS(3, 2, 2)}, {hs: bmHS(3, 2, 2), ents: []*raftpb.Entry{bmEnt(3, 3, 0, 5, r)}}, {hs: bmHS(3, 2, 3)}})
	// the stale stream holds state records where the new one has entries (and vice versa)
	add("entry-over-state",
		[]bmOp{{hs: bmHS(1, 1, 2), ents: []*raftpb.Entry{bmEnt(3, 1, 0, 0, r)}}, {hs: bmHS(1, 1, 3)}},
		[]bmOp{{hs: bmHS(1, 2, 2)}, {hs: bmHS(1, 1, 3)}, {hs: bmHS(1, 1, 2), ents: []*raftpb.Entry{bmEnt(3, 1, 0, 0, r)}}})
	add("entries-over-entries",
		[]bmOp{{hs: bmHS(1, 1, 2), ents: []*raftpb.Entry{bmEnt(3, 1, 0, 50, r), bmEnt(4, 1, 0, 50, r)}}},
		[]bmOp{{hs: bmHS(1, 1, 2), ents: []*raftpb.Entry{bmEnt(3, 1, 0, 50, r), bmEnt(4, 1, 0, 50, r), bmEnt(5, 1, 0, 50, r)}}})
	return out
}

// ---- the enumeration ----

type bmCase struct {
	sc        string
	k         int
	old       string
	size      int64
	newImg    []byte // the whole written image (prefix + tail)
	oldImg    []byte // what each tail byte (and the bytes past it) was before
	s, e      int64  // the tail [s, e)
	nonD      []int64
	frameNonD [][]int64
	allPos    []int64
	recs      []bmRec
	nsync     int // records before s
	allow     map[string]bool
	// the stale stream's records and restart outcomes (old = stale+0 only): an image the stale
	// stream alone explains is the lost-zeroing case (nonissues/etcd-wal-readall-zero-unsynced)
	staleRecs  []bmRec
	allowStale map[string]bool
}

type bmStats struct {
	mu       sync.Mutex
	images   int64
	kinds    map[string]int64
	wrong    []string
	nonpre   map[string]int64 // record-level non-prefix outcomes (by restart outcome)
	checked  int64
	wrongN   map[string]int
	mismatch []string
}

func (st *bmStats) add(kind string, n int64) {
	st.mu.Lock()
	st.kinds[kind] += n
	st.mu.Unlock()
}

func bmEval(t testing.TB, c *bmCase, img []byte, st *bmStats, desc func() string) {
	o := bmRestartMem(img, c.size)
	// record level: the decoded records must be a prefix of the written ones, at least the synced ones
	prefix := len(o.recs) <= len(c.recs)
	for i := 0; prefix && i < len(o.recs); i++ {
		prefix = o.recs[i].eq(c.recs[i])
	}
	kind := o.kind
	if o.kind == "ok" {
		if !c.allow[o.key()] {
			kind = "WRONG"
			spre := len(c.staleRecs) > 0 && len(o.recs) <= len(c.staleRecs)
			for i := 0; spre && i < len(o.recs); i++ {
				spre = o.recs[i].eq(c.staleRecs[i])
			}
			if spre && c.allowStale[o.key()] {
				kind = "ok-stale-prefix"
			}
		} else if !prefix || len(o.recs) < c.nsync {
			kind = "ok-nonprefix-records"
		}
	} else if !prefix && o.stopOK {
		kind = o.kind + "-nonprefix-records"
	}
	oc := c.old
	if strings.HasPrefix(oc, "stale+") && oc != "stale+0" {
		oc = "stale-shifted"
	}
	st.mu.Lock()
	st.images++
	st.kinds[oc+" "+kind]++
	if !prefix && o.stopOK {
		w := o.why
		if i := strings.Index(w, " in file"); i > 0 {
			w = w[:i]
		}
		if len(w) > 60 {
			w = w[:60]
		}
		st.nonpre[oc+" "+o.kind+": "+w]++
	}
	st.mu.Unlock()
	st.mu.Lock()
	sample := st.images%4999 == 0
	st.mu.Unlock()
	if sample {
		real := bmRestartReal(t, img, c.size)
		st.mu.Lock()
		st.checked++
		if real.kind != o.kind || (o.kind == "ok" && real.key() != o.key()) {
			st.mismatch = append(st.mismatch, fmt.Sprintf("%s k=%d old=%s %s: mem %s %s / real %s %s", c.sc, c.k, c.old, desc(), o.kind, o.why, real.kind, real.why))
		}
		st.mu.Unlock()
	}
	st.mu.Lock()
	full := st.wrongN[oc] >= 15
	st.mu.Unlock()
	if kind == "WRONG" && !full {
		real := bmRestartReal(t, img, c.size)
		st.mu.Lock()
		if st.wrongN[oc] < 15 {
			st.wrongN[oc]++
			st.wrong = append(st.wrong, fmt.Sprintf("%s k=%d old=%s %s\n  mem: %s\n  real: %s %s %s", c.sc, c.k, c.old, desc(), bmShort(o), real.kind, real.why, bmShort(real)))
		}
		st.mu.Unlock()
	}
}

func bmMix(c *bmCase, choose func(p int64) bool) []byte {
	img := make([]byte, len(c.oldImg))
	copy(img, c.oldImg)
	copy(img[:c.s], c.newImg[:c.s])
	for p := c.s; p < c.e; p++ {
		if choose(p) {
			img[p] = c.newImg[p]
		}
	}
	return img
}

func bmBuildCases(t testing.TB) []*bmCase {
	var cases []*bmCase
	for _, sc := range bmScenarios() {
		nb, size := bmWrite(t, sc.ops)
		recs, ends := bmFrames(t, nb, size)
		sb, _ := bmWrite(t, sc.stale)
		srecs, sends := bmFrames(t, sb, size)
		allowStale := map[string]bool{}
		for m := range srecs {
			allowStale[bmRestartMem(sb[:sends[m]], size).key()] = true
		}
		for k := 1; k <= 3 && k < len(recs)-3; k++ {
			s, e := ends[len(recs)-k-1], ends[len(recs)-1]
			// what restarts after a clean cut at each record boundary from the synced one return
			allow := map[string]bool{}
			for m := len(recs) - k - 1; m < len(recs); m++ {
				trunc := nb[:ends[m]]
				o := bmRestartMem(trunc, size)
				allow[o.key()] = true
			}
			var nonD, all []int64
			var frameOf []int64
			off := s
			for i := len(recs) - k; i < len(recs); i++ {
				fe := ends[i]
				l := int64(nb[off]) | int64(nb[off+1])<<8 | int64(nb[off+2])<<16
				dl := int64(len(recs[i].data))
				dataStart := off + 8 + l - dl
				if !bytes.Equal(nb[dataStart:off+8+l], recs[i].data) {
					t.Fatalf("%s: data is not the record's last bytes", sc.name)
				}
				for p := off; p < fe; p++ {
					all = append(all, p)
					frameOf = append(frameOf, int64(i))
					if p < dataStart || p >= off+8+l {
						nonD = append(nonD, p)
					}
				}
				off = fe
			}
			olds := []struct {
				name string
				img  []byte
			}{{"zero", make([]byte, len(nb)+2048)}}
			for _, delta := range []int64{0, 8, 16, 24, 40} {
				o := make([]byte, len(nb)+2048)
				copy(o, nb[:s])
				for p := s; p < int64(len(o)); p++ {
					if q := p + delta; q < int64(len(sb)) {
						o[p] = sb[q]
					}
				}
				// the stale image differs from zero only if the stale stream reaches past s
				if q := s + delta; q < int64(len(sb)) {
					olds = append(olds, struct {
						name string
						img  []byte
					}{fmt.Sprintf("stale+%d", delta), o})
				}
			}
			for _, od := range olds {
				c := &bmCase{sc: sc.name, k: k, old: od.name, size: size, newImg: nb, oldImg: od.img, s: s, e: e, recs: recs, nsync: len(recs) - k, allow: allow}
				if od.name == "stale+0" {
					c.staleRecs, c.allowStale = srecs, allowStale
				}
				c.frameNonD = make([][]int64, k)
				for _, p := range nonD {
					if c.oldImg[p] != nb[p] {
						c.nonD = append(c.nonD, p)
						f := frameOf[p-s] - int64(len(recs)-k)
						c.frameNonD[f] = append(c.frameNonD[f], p)
					}
				}
				for _, p := range all {
					if c.oldImg[p] != nb[p] {
						c.allPos = append(c.allPos, p)
					}
				}
				cases = append(cases, c)
			}
		}
	}
	return cases
}

func TestWALByteMix(t *testing.T) {
	old := SegmentSizeBytes
	SegmentSizeBytes = 256 * 1024
	defer func() { SegmentSizeBytes = old }()

	cases := bmBuildCases(t)
	st := &bmStats{kinds: map[string]int64{}, nonpre: map[string]int64{}, wrongN: map[string]int{}}
	maxBits := 20
	if testing.Short() {
		maxBits = 12
	}
	type job struct{ c *bmCase }
	jobs := make(chan job)
	var wg sync.WaitGroup
	for w := 0; w < 8; w++ {
		wg.Add(1)
		go func() {
			defer wg.Done()
			for j := range jobs {
				bmRunCase(t, j.c, st, maxBits)
			}
		}()
	}
	for _, c := range cases {
		jobs <- job{c}
	}
	close(jobs)
	wg.Wait()

	var ks []string
	for k := range st.kinds {
		ks = append(ks, k)
	}
	sort.Strings(ks)
	t.Logf("cases %d, images %d", len(cases), st.images)
	for _, k := range ks {
		t.Logf("  %-28s %d", k, st.kinds[k])
	}
	ks = ks[:0]
	for k := range st.nonpre {
		ks = append(ks, k)
	}
	sort.Strings(ks)
	t.Logf("record-level non-prefix outcomes (decoder accepted a record not written there):")
	for _, k := range ks {
		t.Logf("  %-70s %d", k, st.nonpre[k])
	}
	t.Logf("real-file cross-checks %d, mismatches %d", st.checked, len(st.mismatch))
	for i, m := range st.mismatch {
		if i < 10 {
			t.Logf("  mismatch: %s", m)
		}
	}
	for _, w := range st.wrong {
		t.Errorf("accepted with wrong content: %s", w)
	}
}

func bmRunCase(t testing.TB, c *bmCase, st *bmStats, maxBits int) {
	// exhaustive over the non-Data bytes: subsets of nonD kept old, every other byte new.
	// Too many: per frame, the others all new, then all old after it.
	groups := [][]int64{c.nonD}
	if len(c.nonD) > maxBits {
		groups = c.frameNonD
	}
	for _, g := range groups {
		if len(g) > maxBits {
			// split further: windows of maxBits consecutive non-Data bytes
			for i := 0; i < len(g); i += maxBits / 2 {
				j := i + maxBits
				if j > len(g) {
					j = len(g)
				}
				bmExhaust(t, c, g[i:j], st)
			}
			continue
		}
		bmExhaust(t, c, g, st)
	}
	// with all Data bytes old too (only the non-Data choices new): the frame of zeros/stale data
	for mask := 0; mask < 1<<min(len(c.nonD), 12); mask++ {
		keepNew := map[int64]bool{}
		for i := 0; i < min(len(c.nonD), 12); i++ {
			if mask&(1<<i) != 0 {
				keepNew[c.nonD[i]] = true
			}
		}
		img := bmMix(c, func(p int64) bool { return keepNew[p] })
		bmEval(t, c, img, st, func() string { return fmt.Sprintf("only-nonData-new mask=%x", mask) })
	}
	// sequential tears: new up to a cut point, old after; and per 512-byte chunk
	for cut := c.s; cut <= c.e; cut++ {
		img := bmMix(c, func(p int64) bool { return p < cut })
		cc := cut
		bmEval(t, c, img, st, func() string { return fmt.Sprintf("cut at %d", cc) })
	}
	// random over the whole tail
	r := rand.New(rand.NewSource(int64(c.s)*131 + int64(c.k)*7 + int64(len(c.old))))
	n := 20000
	if testing.Short() {
		n = 1000
	}
	for i := 0; i < n; i++ {
		pr := []float64{0.5, 0.1, 0.02, 0.9, 0.98}[i%5]
		seed := r.Int63()
		rr := rand.New(rand.NewSource(seed))
		img := bmMix(c, func(p int64) bool { return rr.Float64() < pr })
		bmEval(t, c, img, st, func() string { return fmt.Sprintf("random p=%v seed=%d", pr, seed) })
	}
}

func bmExhaust(t testing.TB, c *bmCase, g []int64, st *bmStats) {
	for mask := 0; mask < 1<<len(g); mask++ {
		keepOld := map[int64]bool{}
		for i, p := range g {
			if mask&(1<<i) != 0 {
				keepOld[p] = true
			}
		}
		img := bmMix(c, func(p int64) bool { return !keepOld[p] })
		m := mask
		bmEval(t, c, img, st, func() string {
			var s []string
			for i, p := range g {
				if m&(1<<i) != 0 {
					s = append(s, fmt.Sprintf("%d:%02x->%02x", p-c.s, c.newImg[p], c.oldImg[p]))
				}
			}
			return "old at tail offsets " + strings.Join(s, ",")
		})
	}
}

func bmShort(o bmOutcome) string {
	if o.kind != "ok" {
		return o.kind
	}
	var idx []string
	for _, e := range o.ents {
		idx = append(idx, fmt.Sprintf("%d/%d/%d/%dB", e.GetIndex(), e.GetTerm(), e.GetType(), len(e.GetData())))
	}
	return fmt.Sprintf("hs={%s} start={%s} snaps=%d ents=[%s]", o.hs.String(), o.start.String(), len(o.snaps), strings.Join(idx, " "))
}
