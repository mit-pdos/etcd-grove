package tpdifftest_test

import (
	"encoding/json"
	"fmt"
	"math/rand"
	"sort"
	"strings"
	"sync"
	"testing"

	cmap "github.com/orcaman/concurrent-map"
)

// The concurrent-map model (models/concurrent-map) against concurrent-map v1.0.0: random sequences
// of the operations the kits use (New, GetShard, Set, Upsert, Get, Has, Remove, IterCb,
// Count, IsEmpty) under
// several SHARD_COUNTs, each outcome written to the transcript (run.sh compares the real
// library's with the model's) and checked against a reference (a Go map) in either build; and
// concurrent runs whose final contents are deterministic.

func cmKey(rng *rand.Rand, n int) string {
	return fmt.Sprintf("k%d", rng.Intn(n))
}

// cmShard is the index of key's shard in m (GetShard's pointer among m's).
func cmShard(m cmap.ConcurrentMap, key string) int {
	s := m.GetShard(key)
	for i := range m {
		if m[i] == s {
			return i
		}
	}
	return -1
}

// cmDump is m's contents as IterCb visits them: per shard (in IterCb's order of shards; a
// shard's entries sorted, Go's map order being random), checking that each entry's shard is
// GetShard's for its key.
func cmDump(t *testing.T, m cmap.ConcurrentMap) (string, map[string]interface{}) {
	type kv struct {
		shard int
		key   string
		val   interface{}
	}
	var visits []kv
	all := map[string]interface{}{}
	m.IterCb(func(k string, v interface{}) {
		visits = append(visits, kv{cmShard(m, k), k, v})
		all[k] = v
	})
	for i := 1; i < len(visits); i++ {
		if visits[i].shard < visits[i-1].shard {
			t.Fatalf("IterCb visits shard %d after shard %d", visits[i].shard, visits[i-1].shard)
		}
	}
	sort.SliceStable(visits, func(i, j int) bool {
		if visits[i].shard != visits[j].shard {
			return visits[i].shard < visits[j].shard
		}
		return visits[i].key < visits[j].key
	})
	var b strings.Builder
	for _, e := range visits {
		fmt.Fprintf(&b, "%d:%s=%v ", e.shard, e.key, e.val)
	}
	return b.String(), all
}

func TestCmapRandom(t *testing.T) {
	tr := newTranscript("cmap")
	defer func(n int) { cmap.SHARD_COUNT = n }(cmap.SHARD_COUNT)
	tr.printf("default SHARD_COUNT %d", cmap.SHARD_COUNT)
	rng := rand.New(rand.NewSource(3))
	seqs, ops := 0, 0
	for _, shards := range []int{1, 2, 7, 32, 64, 32768} {
		cmap.SHARD_COUNT = shards
		nseq := 300
		if shards == 32768 {
			nseq = 10
		}
		for s := 0; s < nseq; s++ {
			seqs++
			keys := 1 + rng.Intn(40)
			n := rng.Intn(120)
			tr.printf("shards %d seq %d keys %d ops %d", shards, s, keys, n)
			m := cmap.New()
			if len(m) != shards {
				t.Fatalf("New: %d shards; SHARD_COUNT %d", len(m), shards)
			}
			ref := map[string]interface{}{}
			for i := 0; i < n; i++ {
				ops++
				k := cmKey(rng, keys)
				switch op := rng.Intn(13); {
				case op < 3:
					v := rng.Intn(100)
					m.Set(k, v)
					ref[k] = v
					tr.printf(" set %s %d shard %d", k, v, cmShard(m, k))
				case op < 5:
					nv := rng.Intn(100)
					var saw string
					res := m.Upsert(k, nv, func(exist bool, inMap, newV interface{}) interface{} {
						saw = fmt.Sprintf("%v %v %v", exist, inMap, newV)
						if exist {
							return inMap.(int) + newV.(int)
						}
						return newV
					})
					rv, rok := ref[k]
					if rok {
						ref[k] = rv.(int) + nv
					} else {
						ref[k] = nv
					}
					if fmt.Sprint(rok, " ", rv, " ", nv) != saw || res != ref[k] {
						t.Fatalf("Upsert(%s, %d): cb saw %q, res %v; reference %v %v, %v", k, nv, saw, res, rok, rv, ref[k])
					}
					tr.printf(" upsert %s %d: cb saw %s -> %v", k, nv, saw, res)
				case op < 7:
					v, ok := m.Get(k)
					rv, rok := ref[k]
					if ok != rok || v != rv {
						t.Fatalf("Get(%s) = %v %v; reference %v %v", k, v, ok, rv, rok)
					}
					tr.printf(" get %s = %v %v", k, v, ok)
				case op < 9:
					ok := m.Has(k)
					_, rok := ref[k]
					if ok != rok {
						t.Fatalf("Has(%s) = %v; reference %v", k, ok, rok)
					}
					tr.printf(" has %s = %v", k, ok)
				case op < 11:
					m.Remove(k)
					delete(ref, k)
					tr.printf(" remove %s", k)
				case op < 12:
					c, e := m.Count(), m.IsEmpty()
					if c != len(ref) || e != (len(ref) == 0) {
						t.Fatalf("Count %d IsEmpty %v; reference %d", c, e, len(ref))
					}
					tr.printf(" count %d empty %v", c, e)
				default:
					d, all := cmDump(t, m)
					if fmt.Sprint(all) != fmt.Sprint(ref) {
						t.Fatalf("IterCb saw %v; reference %v", all, ref)
					}
					tr.printf(" itercb %s", d)
				}
			}
			d, _ := cmDump(t, m)
			tr.printf(" final %s", d)
		}
	}
	// SHARD_COUNT changed after New: GetShard reads it (a smaller count: the first shards; a
	// larger one: an index out of range)
	cmap.SHARD_COUNT = 8
	m := cmap.New()
	cmap.SHARD_COUNT = 3
	m.Set("a", 1)
	m.Set("b", 2)
	d, _ := cmDump(t, m)
	tr.printf("shrunk: %s", d)
	cmap.SHARD_COUNT = 9
	tr.printf("grown: set: %s", outcome(func() {
		for i := 0; i < 64; i++ {
			m.Set(fmt.Sprint(i), i)
		}
	}))
	tr.printf("sequences %d operations %d", seqs, ops)
	t.Logf("cmap: %d sequences, %d operations", seqs, ops)
	tr.save(t)
}

// TestCmapConcurrent: goroutines doing Set/Remove on keys of their own and Upsert increments on
// shared keys, with IterCb and Has readers; the final contents are deterministic.
func TestCmapConcurrent(t *testing.T) {
	tr := newTranscript("cmap-concurrent")
	defer func(n int) { cmap.SHARD_COUNT = n }(cmap.SHARD_COUNT)
	for _, shards := range []int{1, 4, 32} {
		cmap.SHARD_COUNT = shards
		for run := 0; run < 20; run++ {
			m := cmap.New()
			const workers, iters = 8, 400
			var wg sync.WaitGroup
			for w := 0; w < workers; w++ {
				wg.Add(1)
				go func(w int) {
					defer wg.Done()
					rng := rand.New(rand.NewSource(int64(1000*run + w)))
					for i := 0; i < iters; i++ {
						own := fmt.Sprintf("w%d-%d", w, rng.Intn(10))
						switch rng.Intn(5) {
						case 0:
							m.Set(own, i)
						case 1:
							m.Remove(own)
						case 2:
							m.Upsert(fmt.Sprintf("shared%d", i%5), 1,
								func(exist bool, inMap, newV interface{}) interface{} {
									if exist {
										return inMap.(int) + newV.(int)
									}
									return newV
								})
						case 3:
							m.IterCb(func(string, interface{}) {})
						default:
							m.Has(own)
						}
					}
					// a final deterministic write of this worker's keys
					for j := 0; j < 10; j++ {
						m.Set(fmt.Sprintf("w%d-%d", w, j), w*100+j)
					}
				}(w)
			}
			wg.Wait()
			d, _ := cmDump(t, m)
			// the shared counters: the number of Upserts, deterministic per worker seed
			tr.printf("shards %d run %d: %s", shards, run, d)
		}
	}
	tr.save(t)
}

// TestCmapFormats: fmt's printing of a shard (the same struct as v1.0.0's) in both builds; JSON
// (MarshalJSON), outside the model: it blocks forever in the model (not modelled), v1.0.0's JSON otherwise.
func TestCmapFormats(t *testing.T) {
	tr := newTranscript("cmap-formats")
	defer func(n int) { cmap.SHARD_COUNT = n }(cmap.SHARD_COUNT)
	cmap.SHARD_COUNT = 1
	m := cmap.New()
	m.Set("a", 1)
	m.Set("b", "x")
	tr.printf("shard %%v %v", m[0])
	tr.printf("shard %%+v %+v", m[0])
	tr.printf("len %d", len(m))
	nm := notModelled(func() { json.Marshal(m) })
	if model && !nm {
		t.Errorf("model: json.Marshal did not block (not modelled)")
	}
	if !model {
		j, err := json.Marshal(m)
		t.Logf("v1.0.0 json %s %v", j, err)
		if nm || string(j) != `{"a":1,"b":"x"}` {
			t.Errorf("v1.0.0 json %s %v", j, err)
		}
	}
	tr.save(t)
}
