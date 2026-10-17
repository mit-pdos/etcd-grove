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

import "testing"

// TestWatcherGroupChooseNegativeMax: choose with a negative maxWatchers. Before
// etcd-io/etcd#22295 it returns an empty fresh group; with the PR,
// make([]*watcher, 0, maxWatchers) panics ("makeslice: cap out of range").
// Not reachable from etcd (the only caller passes maxWatchersPerSync, 512).
func TestWatcherGroupChooseNegativeMax(t *testing.T) {
	wg := newWatcherGroup()
	wg.add(&watcher{key: []byte("foo"), minRev: 1})
	defer func() {
		if r := recover(); r != nil {
			t.Fatalf("choose(-1, ...) panicked: %v", r)
		}
	}()
	g, _ := wg.choose(-1, 10, 0)
	if g.size() != 0 {
		t.Fatalf("expected an empty group, got %d members", g.size())
	}
}
