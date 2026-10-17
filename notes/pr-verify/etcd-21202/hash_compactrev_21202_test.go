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

package mvcc

import (
	"errors"
	"fmt"
	"testing"

	"go.uber.org/zap/zaptest"

	"go.etcd.io/etcd/pkg/v3/traceutil"
	"go.etcd.io/etcd/server/v3/lease"
	betesting "go.etcd.io/etcd/server/v3/storage/backend/testing"
)

// newHistoryStore puts foo at revisions 2..20 and bar at 21, and, if compactAt > 0,
// compacts at compactAt and waits for the compaction to finish.
func newHistoryStore(t *testing.T, compactAt int64, deleteFooAtEnd bool) *store {
	b, _ := betesting.NewDefaultTmpBackend(t)
	s := NewStore(zaptest.NewLogger(t), b, &lease.FakeLessor{}, StoreConfig{})
	t.Cleanup(func() { cleanup(s, b) })
	for i := 2; i <= 20; i++ {
		s.Put([]byte("foo"), []byte(fmt.Sprintf("v%d", i)), lease.NoLease)
	}
	if deleteFooAtEnd {
		s.DeleteRange([]byte("foo"), nil) // revision 21
	} else {
		s.Put([]byte("bar"), []byte("b"), lease.NoLease) // revision 21
	}
	if compactAt > 0 {
		ch, err := s.Compact(traceutil.TODO(), compactAt)
		if err != nil {
			t.Fatal(err)
		}
		<-ch
	}
	return s
}

// A revision below the store's compaction is hashed, not refused, when the custom
// compact revision is at or below it: HashByRev(5) is ErrCompacted on a store compacted
// at 10, HashByRevWithCompactRev(5, 3) is not, and hashes what the compaction left.
func TestHashByRevWithCompactRevBelowStoreCompaction(t *testing.T) {
	compacted := newHistoryStore(t, 10, false)
	full := newHistoryStore(t, 0, false)

	if _, _, err := compacted.HashStorage().HashByRev(5); !errors.Is(err, ErrCompacted) {
		t.Fatalf("HashByRev(5) on a store compacted at 10: err = %v, want ErrCompacted", err)
	}
	hc, _, errc := compacted.HashStorage().HashByRevWithCompactRev(5, 3)
	hf, _, errf := full.HashStorage().HashByRevWithCompactRev(5, 3)
	t.Logf("compacted at 10: %+v err=%v; uncompacted: %+v err=%v", hc, errc, hf, errf)
	if !errors.Is(errc, ErrCompacted) {
		t.Errorf("HashByRevWithCompactRev(5, 3) on a store compacted at 10: err = %v, want ErrCompacted", errc)
	}
}

// A custom compact revision below the store's compaction gives a hash that is not the
// hash of the requested range: the revisions in (compactRev, storeCompact] are gone, so
// two snapshots of the same history, one compacted, give different hashes with the
// same flags and no error.
func TestHashByRevWithCompactRevBelowStoreCompactionDiffers(t *testing.T) {
	compacted := newHistoryStore(t, 10, false)
	full := newHistoryStore(t, 0, false)
	hc, _, errc := compacted.HashStorage().HashByRevWithCompactRev(15, 3)
	hf, _, errf := full.HashStorage().HashByRevWithCompactRev(15, 3)
	t.Logf("compacted at 10: %+v err=%v; uncompacted: %+v err=%v", hc, errc, hf, errf)
	if errc == nil && errf == nil && hc.Hash != hf.Hash {
		t.Errorf("same history, same (rev 15, compactRev 3), no error, different hashes: %#x vs %#x", hc.Hash, hf.Hash)
	}
}

// Control: with the custom compact revision equal to the compacted snapshot's,
// the two snapshots agree (the comparison the PR is for).
func TestHashByRevWithCompactRevAtStoreCompactionAgrees(t *testing.T) {
	compacted := newHistoryStore(t, 10, false)
	full := newHistoryStore(t, 0, false)
	hc, _, errc := compacted.HashStorage().HashByRevWithCompactRev(15, 10)
	hf, _, errf := full.HashStorage().HashByRevWithCompactRev(15, 10)
	if errc != nil || errf != nil || hc != hf {
		t.Errorf("compacted at 10: %+v err=%v; uncompacted: %+v err=%v", hc, errc, hf, errf)
	}
}

// The same comparison fails when no key is live at the hashed revision (an empty
// Keep set: the hasher then filters nothing, issues/etcd-hash-empty-keep.md), and with
// --compact-rev it hashes the whole uncompacted history below compactRev.
func TestHashByRevWithCompactRevEmptyKeepDisagrees(t *testing.T) {
	compacted := newHistoryStore(t, 10, true)
	full := newHistoryStore(t, 0, true)
	hc, _, errc := compacted.HashStorage().HashByRevWithCompactRev(21, 10)
	hf, _, errf := full.HashStorage().HashByRevWithCompactRev(21, 10)
	t.Logf("compacted at 10: %+v err=%v; uncompacted: %+v err=%v", hc, errc, hf, errf)
	if errc == nil && errf == nil && hc.Hash != hf.Hash {
		t.Errorf("same history, every key deleted at 21, (rev 21, compactRev 10): %#x vs %#x", hc.Hash, hf.Hash)
	}
}

// A compact revision above the hashed revision is refused with an explicit rev, but
// accepted when rev is 0 (the latest revision): the check runs before rev 0 is resolved.
func TestHashByRevWithCompactRevAboveRev(t *testing.T) {
	s := newHistoryStore(t, 0, false)
	cur := s.Rev()
	_, _, errExplicit := s.HashStorage().HashByRevWithCompactRev(cur, cur+100)
	h0, _, err0 := s.HashStorage().HashByRevWithCompactRev(0, cur+100)
	t.Logf("rev %d explicit: err=%v; rev 0: %+v err=%v", cur, errExplicit, h0, err0)
	if (errExplicit == nil) != (err0 == nil) {
		t.Errorf("compactRev %d above the current revision %d: explicit rev err=%v, rev 0 err=%v (result %+v)", cur+100, cur, errExplicit, err0, h0)
	}
}

// Detailed mode's total hash is the plain hash.
func TestHashByRevDetailedTotalMatches(t *testing.T) {
	for _, c := range []struct{ rev, compactRev int64 }{{0, 0}, {15, 3}, {15, 10}, {21, 20}} {
		s := newHistoryStore(t, 0, false)
		d, _, errd := s.HashStorage().HashByRevDetailed(c.rev, c.compactRev)
		h, _, errh := s.HashStorage().HashByRevWithCompactRev(c.rev, c.compactRev)
		if errd != nil || errh != nil || d.TotalHash != h {
			t.Errorf("%+v: detailed %+v err=%v; plain %+v err=%v", c, d.TotalHash, errd, h, errh)
		}
	}
}
