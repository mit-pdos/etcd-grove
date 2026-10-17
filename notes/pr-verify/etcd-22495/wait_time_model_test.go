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

package wait

import (
	"math/rand"
	"testing"
)

// TestWaitTimeModel checks timeList against a reference model on random sequences of Wait and
// Trigger, including triggers below the last one and repeated deadlines: after every operation,
// a channel is closed iff its deadline is at most the deadline of some Trigger since it was
// returned (or it was returned already closed), and Pending is the number of distinct deadlines
// still waiting.
func TestWaitTimeModel(t *testing.T) {
	for seed := int64(0); seed < 200; seed++ {
		r := rand.New(rand.NewSource(seed))
		wt := NewTimeList()
		type waiter struct {
			d        uint64
			ch       <-chan struct{}
			released bool
		}
		var ws []*waiter
		var last uint64
		pending := map[uint64]bool{}
		for op := 0; op < 300; op++ {
			d := uint64(r.Intn(60))
			if r.Intn(3) > 0 {
				w := &waiter{d: d, ch: wt.Wait(d)}
				if last >= d {
					w.released = true
				} else {
					pending[d] = true
				}
				ws = append(ws, w)
			} else {
				wt.Trigger(d)
				last = d
				for _, w := range ws {
					if w.d <= d {
						w.released = true
					}
				}
				for k := range pending {
					if k <= d {
						delete(pending, k)
					}
				}
			}
			for _, w := range ws {
				closed := false
				select {
				case <-w.ch:
					closed = true
				default:
				}
				if closed != w.released {
					t.Fatalf("seed %d op %d: waiter at %d closed=%v, want %v", seed, op, w.d, closed, w.released)
				}
			}
			if n := wt.Pending(); n != len(pending) {
				t.Fatalf("seed %d op %d: Pending()=%d, want %d", seed, op, n, len(pending))
			}
		}
	}
}
