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

// TestHashByRevAcrossPhysicalCompaction and putKeys copied verbatim from
// etcd-io/etcd#22515 (de2627f9f, server/storage/mvcc/hash_test.go), to run
// against etcd-io/etcd#22562.

package mvcc

import (
	"fmt"
	"testing"

	"github.com/stretchr/testify/assert"
	"github.com/stretchr/testify/require"
	"go.uber.org/zap/zaptest"

	"go.etcd.io/etcd/server/v3/lease"
	betesting "go.etcd.io/etcd/server/v3/storage/backend/testing"
)

// HashKV at a revision must not depend on whether the physical compaction to
// that revision has run: members compare it across the cluster, and a member
// may still be deleting compacted revisions when it answers. After the
// compaction finishes, the hash must not change from the hash that earlier
// versions return, so that members of mixed versions agree.
func TestHashByRevAcrossPhysicalCompaction(t *testing.T) {
	for _, tc := range []struct {
		name string
		// setup writes the keys and returns the revision to compact.
		setup func(s *store) int64
		// after runs after the compaction finishes.
		after func(s *store)
		// want is the hash that versions before this test return after the
		// compaction finishes.
		want KeyValueHash
	}{
		{
			name: "every key deleted at the compact revision",
			setup: func(s *store) int64 {
				putKeys(s, "k", 20)
				_, rev := s.DeleteRange([]byte("k"), []byte("l"))
				return rev
			},
			want: KeyValueHash{Hash: 0x40a4756d, CompactRevision: 22, Revision: 22},
		},
		{
			name: "one key not deleted",
			setup: func(s *store) int64 {
				putKeys(s, "k", 20)
				s.Put([]byte("survivor"), []byte("v"), lease.NoLease)
				_, rev := s.DeleteRange([]byte("k"), []byte("l"))
				return rev
			},
			want: KeyValueHash{Hash: 0x145acb52, CompactRevision: 23, Revision: 23},
		},
		{
			name: "every key deleted after the compact revision",
			setup: func(s *store) int64 {
				putKeys(s, "k", 20)
				putKeys(s, "k", 20)
				return s.Rev()
			},
			after: func(s *store) {
				s.DeleteRange([]byte("k"), []byte("l"))
			},
			want: KeyValueHash{Hash: 0x4803ce7, CompactRevision: 41, Revision: 42},
		},
	} {
		t.Run(tc.name, func(t *testing.T) {
			b, _ := betesting.NewDefaultTmpBackend(t)
			s := NewStore(zaptest.NewLogger(t), b, &lease.FakeLessor{}, StoreConfig{})
			defer cleanup(s, b)
			rev := tc.setup(s)

			// Record the compaction, but do not delete revisions yet. A member
			// is in this state until the scheduled compaction finishes.
			_, prev, err := s.updateCompactRev(rev)
			require.NoError(t, err)
			s.kvindex.Compact(rev)
			if tc.after != nil {
				tc.after(s)
			}
			before, _, err := s.hashByRev(0)
			require.NoError(t, err)

			_, err = s.scheduleCompaction(rev, prev)
			require.NoError(t, err)
			after, _, err := s.hashByRev(0)
			require.NoError(t, err)

			assert.Equal(t, tc.want, after, "hash after the compaction")
			assert.Equal(t, after, before, "hash during the compaction")
		})
	}
}

func putKeys(s *store, prefix string, n int) {
	for i := range n {
		s.Put([]byte(fmt.Sprint(prefix, i)), []byte(fmt.Sprint(i)), lease.NoLease)
	}
}
