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

package raft

import "testing"

// TestMaybeAppendMalformed probes raftLog.maybeAppend on appends whose entries are not
// contiguous after prev (outside what a correct leader sends; nothing validates them on the
// MsgApp path). It logs each outcome (result, ok, lastIndex, or the panic) rather than
// asserting, so that the same test runs against the code before and after etcd-io/raft#155;
// see README.md for the output at each revision.
func TestMaybeAppendMalformed(t *testing.T) {
	for _, tc := range []struct {
		name      string
		terms     int // local log: indices 1..terms, all term 1
		committed uint64
		prev      entryID
		idx       []uint64 // indices of the appended entries, all term 1
	}{
		{"duplicate", 10, 3, entryID{term: 1, index: 5}, []uint64{6, 6}},
		{"gap", 3, 0, entryID{term: 1, index: 1}, []uint64{2, 5}},
		{"below-prev", 3, 0, entryID{term: 1, index: 2}, []uint64{1}},
	} {
		t.Run(tc.name, func(t *testing.T) {
			defer func() {
				if r := recover(); r != nil {
					t.Logf("%s: panic: %v", tc.name, r)
				}
			}()
			l := newLog(NewMemoryStorage(), discardLogger)
			ts := make([]uint64, tc.terms)
			for i := range ts {
				ts[i] = 1
			}
			l.append(index(1).terms(ts...)...)
			l.commitTo(tc.committed)
			es := index(1).terms(1)[:0]
			for _, i := range tc.idx {
				es = append(es, index(i).terms(1)...)
			}
			li, ok := l.maybeAppend(logSlice{term: 1, prev: tc.prev, entries: es}, tc.committed)
			t.Logf("%s: result: %d %v lastIndex: %d", tc.name, li, ok, l.lastIndex())
		})
	}
}
