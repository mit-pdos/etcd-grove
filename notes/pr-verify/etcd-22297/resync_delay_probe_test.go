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
	"math"
	"testing"
	"time"
)

// TestResyncDelayProbe checks, over edge values of all three arguments (zero,
// negative and extreme durations and counts), that resyncDelay returns the
// documented value and that the value is accepted by time.Ticker.Reset.
func TestResyncDelayProbe(t *testing.T) {
	durs := []time.Duration{math.MinInt64, -time.Second, -1, 0, 1, time.Millisecond, math.MaxInt64}
	counts := []int{math.MinInt, -1, 0, 1, 2, 512, 1000, math.MaxInt}
	ticker := time.NewTicker(watchResyncPeriod)
	defer ticker.Stop()
	for _, sd := range durs {
		for _, last := range counts {
			for _, un := range counts {
				got := resyncDelay(sd, last, un)
				want := watchResyncPeriod
				if un != 0 && last > un && sd > 0 {
					want = sd
				}
				if got != want || got <= 0 {
					t.Fatalf("resyncDelay(%v, %d, %d) = %v, want %v (> 0)", sd, last, un, got, want)
				}
				ticker.Reset(got) // panics on a non-positive duration
			}
		}
	}
}
