// Reviewer's checks for etcd-io/etcd#22515 (not for upstream). Run the same file at
// the pin and at the PR; the Dump test writes per-seed hashes to $R22515_OUT so the
// two can be diffed.
package mvcc

import (
	"fmt"
	"math/rand"
	"os"
	"strings"
	"sync"
	"testing"
	"time"

	"github.com/stretchr/testify/require"
	"go.uber.org/zap"

	"go.etcd.io/etcd/pkg/v3/traceutil"
	"go.etcd.io/etcd/server/v3/lease"
	betesting "go.etcd.io/etcd/server/v3/storage/backend/testing"
	"go.etcd.io/etcd/server/v3/storage/schema"
)

// r22515Ops: random puts, single deletes, whole-keyspace deletes and multi-op txns
// (no delete and put of the same key in one revision: the API forbids it).
func r22515Ops(s *store, rnd *rand.Rand, n int) {
	keys := []string{"a", "b", "c", "d"}
	for i := 0; i < n; i++ {
		k := []byte(keys[rnd.Intn(len(keys))])
		switch x := rnd.Intn(12); {
		case x == 0:
			s.DeleteRange([]byte("a"), []byte("z"))
		case x == 1:
			// txn: put two distinct keys, delete a third
			p := rnd.Perm(len(keys))
			txn := s.Write(traceutil.TODO())
			txn.Put([]byte(keys[p[0]]), []byte(fmt.Sprint(i)), lease.NoLease)
			txn.Put([]byte(keys[p[1]]), []byte(fmt.Sprint(i)), lease.NoLease)
			txn.DeleteRange([]byte(keys[p[2]]), nil)
			txn.End()
		case x == 2:
			// txn: put then delete the same key (allowed by mvcc; API forbids too, but
			// harmless for compaction: same generation)
			if rnd.Intn(3) == 0 {
				txn := s.Write(traceutil.TODO())
				txn.Put(k, []byte(fmt.Sprint(i)), lease.NoLease)
				txn.DeleteRange(k, nil)
				txn.End()
			} else {
				s.Put(k, []byte(fmt.Sprint(i)), lease.NoLease)
			}
		case x < 6:
			s.DeleteRange(k, nil)
		default:
			s.Put(k, []byte(fmt.Sprint(i)), lease.NoLease)
		}
	}
}

func r22515NewStore(t *testing.T, cfg StoreConfig) (*store, func()) {
	b, _ := betesting.NewDefaultTmpBackend(t)
	s := NewStore(zap.NewNop(), b, &lease.FakeLessor{}, cfg)
	return s, func() { cleanup(s, b) }
}

// r22515History builds a deterministic history from seed: ops, maybe a finished
// compaction at cp, more ops. Returns the store.
func r22515History(t *testing.T, seed int64, cfg StoreConfig) (*store, func(), *rand.Rand) {
	rnd := rand.New(rand.NewSource(seed))
	s, done := r22515NewStore(t, cfg)
	r22515Ops(s, rnd, 1+rnd.Intn(10))
	if s.Rev() >= 2 && rnd.Intn(2) == 0 {
		cp := 1 + rnd.Int63n(s.Rev())
		ch, e := s.Compact(traceutil.TODO(), cp)
		require.NoError(t, e)
		<-ch
	}
	r22515Ops(s, rnd, 1+rnd.Intn(10))
	return s, done, rnd
}

// TestR22515Dump: finished compactions, then HashKV of every revision from the
// compaction revision on; and the compaction-hash check (stored hash of c1 vs
// HashKV(c1) at c0, both at c0 finished). Output diffed between pin and PR.
func TestR22515Dump(t *testing.T) {
	var out strings.Builder
	for seed := int64(0); seed < 3000; seed++ {
		s, done, rnd := r22515History(t, seed, StoreConfig{})
		c0 := s.compactMainRev
		// HashKV(r) for all r in [max(c0,1), cur] after a finished compaction (or none)
		lo := c0
		if lo < 1 {
			lo = 1
		}
		fmt.Fprintf(&out, "seed %d c0 %d cur %d:", seed, c0, s.Rev())
		for r := lo; r <= s.Rev(); r++ {
			h, _, e := s.hashByRev(r)
			require.NoError(t, e)
			fmt.Fprintf(&out, " %d=%08x", r, h.Hash)
		}
		// compaction-hash check at c1
		if s.Rev() > lo {
			c1 := lo + 1 + rnd.Int63n(s.Rev()-lo)
			hX, _, e := s.hashByRev(c1)
			require.NoError(t, e)
			ch, e := s.Compact(traceutil.TODO(), c1)
			require.NoError(t, e)
			<-ch
			stored := s.hashes.Hashes()
			var st KeyValueHash
			for _, h := range stored {
				if h.Revision == c1 {
					st = h
				}
			}
			eq := st == hX
			fmt.Fprintf(&out, " | c1 %d stored==HashKV %v", c1, eq)
			for r := c1; r <= s.Rev(); r++ {
				h, _, e := s.hashByRev(r)
				require.NoError(t, e)
				fmt.Fprintf(&out, " %d=%08x", r, h.Hash)
			}
		}
		out.WriteString("\n")
		done()
	}
	if p := os.Getenv("R22515_OUT"); p != "" {
		require.NoError(t, os.WriteFile(p, []byte(out.String()), 0o644))
	}
}

// deleteSubset deletes from the Key bucket a random subset (or a prefix in
// revision order) of the revisions at or below c not in keep.
func r22515DeleteSubset(s *store, rnd *rand.Rand, c int64, keep map[Revision]struct{}, prefix bool) {
	stop := rnd.Int63n(c + 2)
	tx := s.b.BatchTx()
	tx.LockOutsideApply()
	keys, _ := tx.UnsafeRange(schema.Key, RevToBytes(Revision{Main: 0}, NewRevBytes()),
		RevToBytes(Revision{Main: c + 1}, NewRevBytes()), 0)
	for _, k := range keys {
		r := BytesToRev(k)
		if prefix && r.Main >= stop {
			break
		}
		if _, ok := keep[r]; !ok && (prefix || rnd.Intn(2) == 0) {
			tx.UnsafeDelete(schema.Key, k)
		}
	}
	tx.Unlock()
	s.b.ForceCommit()
}

func r22515HashAll(t *testing.T, s *store, lo int64) []KeyValueHash {
	var hs []KeyValueHash
	for r := lo; r <= s.Rev(); r++ {
		h, _, e := s.hashByRev(r)
		require.NoError(t, e)
		hs = append(hs, h)
	}
	return hs
}

// TestR22515Progress: compaction revision c1 recorded, the index compacted at c1
// or not (the index state is that of a twin store built from the same seed),
// a random subset of c1's deletions done; HashKV(r) for every r in [c1, cur]
// must equal its value after the compaction finishes.
func TestR22515Progress(t *testing.T) {
	fails := 0
	for seed := int64(0); seed < 3000; seed++ {
		if err := r22515ProgressTrial(t, seed); err != nil {
			fails++
			if fails <= 5 {
				t.Logf("seed %d: %v", seed, err)
			}
		}
	}
	t.Logf("%d of 3000 trials fail", fails)
	if fails > 0 {
		t.Errorf("failures")
	}
}

func r22515ProgressTrial(t *testing.T, seed int64) error {
	s, done, rnd := r22515History(t, seed, StoreConfig{})
	defer done()
	twin, done2, _ := r22515History(t, seed, StoreConfig{})
	defer done2()
	lo := s.compactMainRev
	if lo < 0 {
		lo = 0
	}
	if s.Rev() <= lo {
		return nil
	}
	c1 := lo + 1 + rnd.Int63n(s.Rev()-lo)
	idxCompacted := rnd.Intn(2) == 0
	prefix := rnd.Intn(2) == 0
	extra := rnd.Intn(4)
	_, prev, e := s.updateCompactRev(c1)
	require.NoError(t, e)
	var keep map[Revision]struct{}
	if idxCompacted {
		keep = s.kvindex.Compact(c1)
	} else {
		keep = twin.kvindex.Compact(c1)
	}
	r22515Ops(s, rnd, extra)
	h0 := r22515HashAll(t, s, c1)
	r22515DeleteSubset(s, rnd, c1, keep, prefix)
	h1 := r22515HashAll(t, s, c1)
	_, e = s.scheduleCompaction(c1, prev)
	require.NoError(t, e)
	h2 := r22515HashAll(t, s, c1)
	for i := range h2 {
		if h0[i] != h2[i] || h1[i] != h2[i] {
			return fmt.Errorf("c1=%d idxCompacted=%v rev=%d: before deletions %x, partial %x, after %x",
				c1, idxCompacted, c1+int64(i), h0[i].Hash, h1[i].Hash, h2[i].Hash)
		}
	}
	return nil
}

// TestR22515Concurrent: a real compaction (one key per batch, a pause between
// batches) with HashKV of every revision in [c, cur] and writes running
// concurrently; every HashKV with compaction revision c must equal its value after.
func TestR22515Concurrent(t *testing.T) {
	fails := 0
	for seed := int64(0); seed < 300; seed++ {
		if err := r22515ConcTrial(t, seed); err != nil {
			fails++
			if fails <= 5 {
				t.Logf("seed %d: %v", seed, err)
			}
		}
	}
	t.Logf("%d of 300 trials fail", fails)
	if fails > 0 {
		t.Errorf("failures")
	}
}

func r22515ConcTrial(t *testing.T, seed int64) error {
	s, done, rnd := r22515History(t, seed, StoreConfig{CompactionBatchLimit: 1, CompactionSleepInterval: 200 * time.Microsecond})
	defer done()
	lo := s.compactMainRev
	if lo < 0 {
		lo = 0
	}
	if s.Rev() <= lo {
		return nil
	}
	c := lo + 1 + rnd.Int63n(s.Rev()-lo)
	cur := s.Rev()
	ch, e := s.Compact(traceutil.TODO(), c)
	require.NoError(t, e)
	var mu sync.Mutex
	seen := map[int64][]uint32{}
	var wg sync.WaitGroup
	stop := make(chan struct{})
	for g := 0; g < 3; g++ {
		wg.Add(1)
		go func(g int) {
			defer wg.Done()
			for {
				select {
				case <-stop:
					return
				default:
				}
				r := c + int64((g+len(seen))%int(cur-c+1))
				h, _, e := s.hashByRev(r)
				if e != nil || h.CompactRevision != c {
					continue
				}
				mu.Lock()
				seen[r] = append(seen[r], h.Hash)
				mu.Unlock()
			}
		}(g)
	}
	wg.Add(1)
	go func() {
		defer wg.Done()
		for i := 0; i < 20; i++ {
			s.Put([]byte("w"), []byte(fmt.Sprint(i)), lease.NoLease)
			time.Sleep(50 * time.Microsecond)
		}
	}()
	<-ch
	close(stop)
	wg.Wait()
	for r := c; r <= cur; r++ {
		h, _, e := s.hashByRev(r)
		require.NoError(t, e)
		for _, x := range seen[r] {
			if x != h.Hash {
				return fmt.Errorf("c=%d rev=%d: during %x after %x (%d samples)", c, r, x, h.Hash, len(seen[r]))
			}
		}
	}
	return nil
}

// TestR22515Symptom1: the Lean counterexample hashIncl22515_keep_compact_differ:
// put k at 2, delete it at 3; a member at compaction revision 2 answers HashKV(3);
// a member that ran Compact(3) stored the job's hash of 3 (compact revision 2).
func TestR22515Symptom1(t *testing.T) {
	s, done := r22515NewStore(t, StoreConfig{})
	defer done()
	s.Put([]byte("k"), []byte("v"), lease.NoLease) // rev 2
	s.DeleteRange([]byte("k"), nil)                 // rev 3
	ch, e := s.Compact(traceutil.TODO(), 2)
	require.NoError(t, e)
	<-ch
	hX, _, e := s.hashByRev(3)
	require.NoError(t, e)
	ch, e = s.Compact(traceutil.TODO(), 3)
	require.NoError(t, e)
	<-ch
	hs := s.hashes.Hashes()
	st := hs[len(hs)-1]
	t.Logf("HashKV(3) at c=2: %+v; stored hash of 3: %+v", hX, st)
	require.Equal(t, st, hX)
}
