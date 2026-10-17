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

package cache

// Probes of etcd-io/etcd#21676's ringBuffer helpers (run in cache/ of the PR head, next to
// the PR's ringbuffer_test.go, whose helpers they use).

import (
	"testing"
	"time"
)

// ReplaceLatest does not check that the new item's revision keeps the buffer sorted. With
// a revision below the previous entry's, the binary searches every iteration method relies
// on give wrong answers: AscendGreaterOrEqual(4) visits revision 3.
func TestReplaceLatestBreaksOrdering(t *testing.T) {
	rb := setupRingBuffer(t, 4, []int64{5, 10})
	batch, err := makeEventBatch(3, "key", 1)
	if err != nil {
		t.Fatal(err)
	}
	rb.ReplaceLatest(batch) // stored revisions are now 5, 3

	for _, rev := range collectRevisions(rb, ascendGTE, 4) {
		if rev < 4 {
			t.Errorf("AscendGreaterOrEqual(4) visited revision %d", rev)
		}
	}
	rb.RemoveLess(4)
	for _, rev := range collectRevisions(rb, ascendGTE, 0) {
		if rev < 4 {
			t.Errorf("after RemoveLess(4), revision %d is still stored", rev)
		}
	}
}

// ensureCapacity's doubling overflows int for a minCapacity above 2^62 when the buffer's
// length is a power of two: newCap goes 2^62, -2^63, 0, 0, ... and the loop never ends.
func TestEnsureCapacityOverflowHangs(t *testing.T) {
	rb := setupRingBuffer(t, 1, []int64{1})
	done := make(chan struct{})
	go func() {
		defer func() { recover(); close(done) }()
		rb.ensureCapacity(1<<62 + 1)
	}()
	select {
	case <-done:
	case <-time.After(2 * time.Second):
		t.Errorf("ensureCapacity(1<<62 + 1) has not returned after 2s (newCap overflowed to 0)")
	}
}
