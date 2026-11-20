// The same tests against the real github.com/orcaman/concurrent-map v1.0.0 and against the lab's
// model (run.sh): random sequences of the operations the model keeps, checked against a Go map;
// the shard of every key (v1.0.0's fnv32, modulo SHARD_COUNT); IterCb's visits; and concurrent
// use (-race).
package cmapdifftest

import (
	"fmt"
	"math/rand"
	"sort"
	"sync"
	"testing"

	cmap "github.com/orcaman/concurrent-map"
)

func fnv(key string) uint32 {
	h := uint32(2166136261)
	for i := 0; i < len(key); i++ {
		h *= 16777619
		h ^= uint32(key[i])
	}
	return h
}

func keys(m map[string]interface{}) []string {
	var ks []string
	for k := range m {
		ks = append(ks, k)
	}
	sort.Strings(ks)
	return ks
}

func TestSequential(t *testing.T) {
	for _, shards := range []int{1, 2, 32, 32768} {
		cmap.SHARD_COUNT = shards
		r := rand.New(rand.NewSource(int64(shards)))
		for round := 0; round < 20; round++ {
			m := cmap.New()
			if len(m) != shards {
				t.Fatalf("New: %d shards, want %d", len(m), shards)
			}
			ref := map[string]interface{}{}
			for i := 0; i < 300; i++ {
				k := fmt.Sprintf("%d,%d", r.Intn(5), r.Intn(8))
				if m.GetShard(k) != m[uint(fnv(k))%uint(shards)] {
					t.Fatalf("GetShard(%q)", k)
				}
				switch op := r.Intn(10); op {
				case 0:
					m.Set(k, i)
					ref[k] = i
				case 1:
					got := m.Upsert(k, i, func(exist bool, old, nv interface{}) interface{} {
						if exist {
							return old.(int) + nv.(int)
						}
						return nv
					})
					if old, ok := ref[k]; ok {
						ref[k] = old.(int) + i
					} else {
						ref[k] = i
					}
					if got != ref[k] {
						t.Fatalf("Upsert: %v, want %v", got, ref[k])
					}
				case 2:
					_, had := ref[k]
					if m.SetIfAbsent(k, i) == had {
						t.Fatal("SetIfAbsent")
					}
					if !had {
						ref[k] = i
					}
				case 3:
					v, ok := m.Get(k)
					w, ok2 := ref[k]
					if ok != ok2 || v != w {
						t.Fatalf("Get(%q) = %v %v, want %v %v", k, v, ok, w, ok2)
					}
				case 4:
					if _, ok := ref[k]; m.Has(k) != ok {
						t.Fatalf("Has(%q)", k)
					}
				case 5:
					m.Remove(k)
					delete(ref, k)
				case 6:
					rm := r.Intn(2) == 0
					_, had := ref[k]
					got := m.RemoveCb(k, func(key string, v interface{}, exists bool) bool {
						if key != k || exists != had || (had && v != ref[k]) {
							t.Fatalf("RemoveCb's callback: %q %v %v", key, v, exists)
						}
						return rm
					})
					if got != rm {
						t.Fatal("RemoveCb's result")
					}
					if rm {
						delete(ref, k)
					}
				case 7:
					v, ok := m.Pop(k)
					w, ok2 := ref[k]
					if ok != ok2 || v != w {
						t.Fatalf("Pop(%q)", k)
					}
					delete(ref, k)
				case 8:
					data := map[string]interface{}{k: i, k + "x": -i}
					m.MSet(data)
					ref[k], ref[k+"x"] = i, -i
				case 9:
					if m.Count() != len(ref) || m.IsEmpty() != (len(ref) == 0) {
						t.Fatalf("Count %d IsEmpty %v, want %d", m.Count(), m.IsEmpty(), len(ref))
					}
				}
			}
			seen := map[string]interface{}{}
			m.IterCb(func(k string, v interface{}) {
				if _, dup := seen[k]; dup {
					t.Fatalf("IterCb visits %q twice", k)
				}
				seen[k] = v
			})
			if fmt.Sprint(keys(seen)) != fmt.Sprint(keys(ref)) {
				t.Fatalf("IterCb: %v, want %v", keys(seen), keys(ref))
			}
			for k, v := range ref {
				if seen[k] != v {
					t.Fatalf("IterCb's value of %q", k)
				}
			}
		}
	}
	cmap.SHARD_COUNT = 32
}

func TestConcurrent(t *testing.T) {
	cmap.SHARD_COUNT = 32768
	m := cmap.New()
	var wg sync.WaitGroup
	for g := 0; g < 8; g++ {
		wg.Add(1)
		go func(g int) {
			defer wg.Done()
			for i := 0; i < 500; i++ {
				k := fmt.Sprintf("%d,%d", g, i%50)
				m.Upsert(k, 1, func(exist bool, old, nv interface{}) interface{} {
					if exist {
						return old.(int) + 1
					}
					return nv
				})
				m.Has(k)
				if i%7 == 0 {
					m.Remove(k)
				}
				m.IterCb(func(string, interface{}) {})
			}
		}(g)
	}
	wg.Wait()
	cmap.SHARD_COUNT = 32
}
