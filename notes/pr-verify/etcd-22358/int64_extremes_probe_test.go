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

package adt

import (
	"math"
	"math/rand"
	"testing"
)

// TestProbeInt64ExtremesTree shows the comparator wrap through the tree's API: an interval
// tree with [MinInt64, 0) and [0, MaxInt64) answers stabbing queries wrongly when
// Compare wraps (base), and correctly with etcd#22358 (head).
func TestProbeInt64ExtremesTree(t *testing.T) {
	ivt := NewIntervalTree()
	ivt.Insert(NewInt64Interval(math.MinInt64, 0), "neg")
	ivt.Insert(NewInt64Interval(0, math.MaxInt64), "nonneg")
	for _, tc := range []struct {
		p    int64
		want string
	}{{math.MinInt64, "neg"}, {-1, "neg"}, {0, "nonneg"}, {math.MaxInt64 - 1, "nonneg"}} {
		got := ivt.Stab(NewInt64Point(tc.p))
		if len(got) != 1 || got[0].Val != tc.want {
			vals := []any{}
			for _, g := range got {
				vals = append(vals, g.Val)
			}
			t.Errorf("Stab(%d) = %v, want [%s]", tc.p, vals, tc.want)
		}
	}
	// MaxInt64 is in no half-open int64 interval.
	if got := ivt.Stab(NewInt64Point(math.MaxInt64)); len(got) != 0 {
		t.Errorf("Stab(MaxInt64) = %d results, want 0", len(got))
	}
	if ivt.Intersects(NewInt64Point(math.MaxInt64)) {
		t.Errorf("Intersects(MaxInt64) = true, want false")
	}
}

// TestProbeInt64ExtremesRandom checks Stab against a brute-force containment over intervals
// with endpoints drawn from values near both ends of int64 and near zero.
func TestProbeInt64ExtremesRandom(t *testing.T) {
	pool := []int64{math.MinInt64, math.MinInt64 + 1, -1 << 62, -2, -1, 0, 1, 2, 1 << 62,
		math.MaxInt64 - 2, math.MaxInt64 - 1, math.MaxInt64}
	r := rand.New(rand.NewSource(1))
	fails := 0
	for iter := 0; iter < 2000 && fails < 3; iter++ {
		ivt := NewIntervalTree()
		type iv struct{ b, e int64 }
		var ivs []iv
		for k := 0; k < 6; k++ {
			b, e := pool[r.Intn(len(pool))], pool[r.Intn(len(pool))]
			if b >= e {
				continue
			}
			ivt.Insert(NewInt64Interval(b, e), len(ivs))
			ivs = append(ivs, iv{b, e})
		}
		for _, p := range pool {
			want := 0
			for _, x := range ivs {
				if x.b <= p && p < x.e {
					want++
				}
			}
			if got := len(ivt.Stab(NewInt64Point(p))); got != want {
				t.Errorf("intervals %v: Stab(%d) has %d results, want %d", ivs, p, got, want)
				fails++
			}
		}
	}
}
