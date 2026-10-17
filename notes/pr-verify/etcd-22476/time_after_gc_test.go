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
	"runtime"
	"testing"
	"time"
)

// TestTimeAfterInSelectIsCollected checks the premise of the timer-leak part of
// etcd-io/etcd#22476: that a time.After timer abandoned by a select whose other
// case fires stays alive until it expires. Since Go 1.23 (this module's go
// directive is 1.27), an unreferenced timer is collected before it fires, so
// 1e6 abandoned one-hour timers must not keep the heap grown.
func TestTimeAfterInSelectIsCollected(t *testing.T) {
	ready := make(chan struct{})
	close(ready)
	var before, after runtime.MemStats
	runtime.GC()
	runtime.ReadMemStats(&before)
	for i := 0; i < 1_000_000; i++ {
		select {
		case <-time.After(time.Hour):
		case <-ready:
		}
	}
	runtime.GC()
	runtime.ReadMemStats(&after)
	grown := int64(after.HeapInuse) - int64(before.HeapInuse)
	t.Logf("heap in use: before %d, after %d (grown %d bytes)", before.HeapInuse, after.HeapInuse, grown)
	if grown > 16<<20 {
		t.Fatalf("1e6 abandoned time.After timers kept %d bytes alive", grown)
	}
}
