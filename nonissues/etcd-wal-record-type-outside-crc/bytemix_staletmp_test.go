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

import (
	"fmt"
	"math/rand"
	"os"
	"path/filepath"
	"sort"
	"testing"

	"github.com/stretchr/testify/require"
	"go.uber.org/zap"

	"go.etcd.io/etcd/client/pkg/v3/fileutil"
	"go.etcd.io/etcd/pkg/v3/pbutil"
	"go.etcd.io/etcd/server/v3/storage/wal/walpb"
	"go.etcd.io/raft/v3/raftpb"
)

// bmStaleTmp builds the reused-N.tmp state of nonissues/etcd-wal-cut-reuses-stale-tmp (an
// interrupted cut left old headers in 0.tmp; the next incarnation's cut writes shorter headers over
// them), then appends one Save (entries and a hard state) to the new segment. It returns the first
// segment (whole), the new segment as the cut left it (synced: headers, the stale remnant, zeros),
// the new segment after the Save, and the segment size.
func bmStaleTmp(t testing.TB, oldHS, newHS, saveHS *raftpb.HardState, oldPrevCrc uint32, ents []*raftpb.Entry) (seg0, before, after []byte, size int64) {
	old := SegmentSizeBytes
	defer func() { SegmentSizeBytes = old }()
	SegmentSizeBytes = 256 * 1024
	lg := zap.NewNop()
	tmp, err := os.MkdirTemp("", "bytemix-tmp")
	require.NoError(t, err)
	defer os.RemoveAll(tmp)
	dir := filepath.Join(tmp, "w")
	md := []byte("metadata")
	ent := func(i uint64) *raftpb.Entry {
		return &raftpb.Entry{Term: new(uint64(1)), Index: new(i), Data: []byte("data")}
	}
	w, err := Create(lg, dir, md)
	require.NoError(t, err)
	require.NoError(t, w.Save(oldHS, []*raftpb.Entry{ent(1), ent(2)}))
	require.NoError(t, w.Close())
	f, err := createNewWALFile[*os.File](filepath.Join(dir, "0.tmp"), true)
	require.NoError(t, err)
	require.NoError(t, fileutil.Preallocate(f, SegmentSizeBytes, true))
	enc, err := newFileEncoder(f, oldPrevCrc)
	require.NoError(t, err)
	require.NoError(t, enc.encode(&walpb.Record{Type: new(CrcType), Crc: &oldPrevCrc}))
	require.NoError(t, enc.encode(&walpb.Record{Type: new(MetadataType), Data: md}))
	require.NoError(t, enc.encode(&walpb.Record{Type: new(StateType), Data: pbutil.MustMarshalMessage(oldHS)}))
	require.NoError(t, enc.flush())
	require.NoError(t, f.Sync())
	require.NoError(t, f.Close())

	w, err = Open(lg, dir, &walpb.Snapshot{Index: new(uint64(0)), Term: new(uint64(0))})
	require.NoError(t, err)
	_, _, _, err = w.ReadAll()
	require.NoError(t, err)
	SegmentSizeBytes = 1 // the next Save cuts
	require.NoError(t, w.Save(newHS, []*raftpb.Entry{ent(3)}))
	SegmentSizeBytes = 256 * 1024
	names, err := readWALNames(lg, dir)
	require.NoError(t, err)
	require.Len(t, names, 2)
	p1 := filepath.Join(dir, names[1])
	before, err = os.ReadFile(p1)
	require.NoError(t, err)
	require.NoError(t, w.Save(saveHS, ents))
	require.NoError(t, w.Close())
	after, err = os.ReadFile(p1)
	require.NoError(t, err)
	seg0, err = os.ReadFile(filepath.Join(dir, names[0]))
	require.NoError(t, err)
	return seg0, before, after, int64(len(after))
}

// TestWALByteMixStaleTmp: byte mixes of the first Save after a cut into a reused 0.tmp, whose old
// bytes are the stale remnant of the old headers (then zeros). Random member IDs, terms, commits,
// chain CRCs; exhaustive over the differing non-Data bytes of the Save's frames, plus random mixes.
func TestWALByteMixStaleTmp(t *testing.T) {
	rnd := rand.New(rand.NewSource(7))
	n := 400
	if testing.Short() {
		n = 60
	}
	kinds := map[string]int{}
	var wrong []string
	images, withRemnant := 0, 0
	for i := 0; i < n; i++ {
		term := uint64(rnd.Intn(1 << uint(1+rnd.Intn(30))))
		oldHS := &raftpb.HardState{Term: new(term), Vote: new(rnd.Uint64() | 1<<uint(rnd.Intn(64))), Commit: new(uint64(rnd.Intn(1 << uint(1+rnd.Intn(40)))))}
		newHS := &raftpb.HardState{Term: new(term + 1), Vote: new(uint64(0)), Commit: new(oldHS.GetCommit())}
		saveHS := &raftpb.HardState{Term: new(term + 1), Vote: new(uint64(2)), Commit: new(oldHS.GetCommit())}
		typ := []*raftpb.EntryType{nil, new(raftpb.EntryNormal), new(raftpb.EntryConfChange)}[rnd.Intn(3)]
		var ents []*raftpb.Entry
		for j := uint64(4); j < 4+uint64(1+rnd.Intn(2)); j++ {
			d := make([]byte, rnd.Intn(200))
			rnd.Read(d)
			ents = append(ents, &raftpb.Entry{Term: new(term + 1), Index: new(j), Type: typ, Data: d})
		}
		seg0, before, after, size := bmStaleTmp(t, oldHS, newHS, saveHS, rnd.Uint32(), ents)
		written, ends, err := bmDecode(after, size, seg0)
		require.ErrorContains(t, err, "EOF")
		nApp := len(ents) + 1
		s, e := ends[len(ends)-nApp-1], ends[len(ends)-1]
		remnant := false
		for p := s; p < e; p++ {
			if before[p] != 0 {
				remnant = true
			}
		}
		if remnant {
			withRemnant++
		}
		// the positions where old and new differ; the non-Data ones of each frame
		var diff, nonD []int64
		off := s
		for r := len(written) - nApp; r < len(written); r++ {
			fe := ends[r]
			l := int64(after[off]) | int64(after[off+1])<<8 | int64(after[off+2])<<16
			ds := off + 8 + l - int64(len(written[r].data))
			for p := off; p < fe; p++ {
				if before[p] != after[p] {
					diff = append(diff, p)
					if p < ds || p >= off+8+l {
						nonD = append(nonD, p)
					}
				}
			}
			off = fe
		}
		eval := func(img []byte, desc func() string) {
			images++
			o := bmRestartMem(img, size, seg0)
			prefix := len(o.recs) <= len(written)
			for j := 0; prefix && j < len(o.recs); j++ {
				prefix = o.recs[j].eq(written[j])
			}
			k := o.kind
			if !prefix && o.stopOK {
				k += "-nonprefix"
				if o.kind == "ok" {
					k = "WRONG"
				} else {
					k += " (" + o.why + ")"
					if len(k) > 90 {
						k = k[:90]
					}
				}
			}
			kinds[k]++
			if k == "WRONG" && len(wrong) < 20 {
				wrong = append(wrong, fmt.Sprintf("case %d old %v new %v save %v: %s\n  read: %s", i, oldHS, newHS, saveHS, desc(), bmShort(o)))
			}
		}
		mix := func(newAt func(p int64) bool) []byte {
			img := append([]byte(nil), before...)
			for _, p := range diff {
				if newAt(p) {
					img[p] = after[p]
				}
			}
			return img
		}
		// exhaustive over the bytes over the stale remnant and the first frame's other non-Data
		// bytes, at most 12 (others new); the rest of the tail is over zeros, as TestWALByteMix's
		// "zero" cases
		var g []int64
		for _, p := range diff {
			if before[p] != 0 && len(g) < 14 {
				g = append(g, p)
			}
		}
		for _, p := range nonD {
			if before[p] == 0 && len(g) < 12 {
				g = append(g, p)
			}
		}
		{
			for mask := 0; mask < 1<<len(g); mask++ {
				oldAt := map[int64]bool{}
				for b, p := range g {
					if mask&(1<<b) != 0 {
						oldAt[p] = true
					}
				}
				m := mask
				eval(mix(func(p int64) bool { return !oldAt[p] }), func() string {
					var d []string
					for b, p := range g {
						if m&(1<<b) != 0 {
							d = append(d, fmt.Sprintf("+%d:%02x->%02x", p-s, after[p], before[p]))
						}
					}
					return fmt.Sprint("old at ", d)
				})
			}
		}
		for j := 0; j < 2000; j++ {
			pr := []float64{0.5, 0.1, 0.9}[j%3]
			seed := rnd.Int63()
			rr := rand.New(rand.NewSource(seed))
			eval(mix(func(int64) bool { return rr.Float64() < pr }), func() string { return fmt.Sprintf("random p=%v seed=%d", pr, seed) })
		}
	}
	var ks []string
	for k := range kinds {
		ks = append(ks, k)
	}
	sort.Strings(ks)
	t.Logf("%d cases (%d with a stale remnant under the Save), %d images", n, withRemnant, images)
	for _, k := range ks {
		t.Logf("  %-90s %d", k, kinds[k])
	}
	for _, w := range wrong {
		t.Errorf("accepted with wrong content: %s", w)
	}
}
