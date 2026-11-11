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
	"testing"

	"github.com/stretchr/testify/assert"
	"github.com/stretchr/testify/require"
	"go.uber.org/zap/zaptest"

	"go.etcd.io/etcd/pkg/v3/traceutil"
	"go.etcd.io/etcd/server/v3/lease"
	betesting "go.etcd.io/etcd/server/v3/storage/backend/testing"
)

// Two members with the same history: the leader has applied a compaction and
// stored its hash; a follower that has applied the same writes but not yet the
// compaction answers HashByRev at that revision with the same compact
// revision. CompactHashCheck compares the two hashes.
func TestHashByRevMatchesCompactionHashWhenKeyspaceEmpty(t *testing.T) {
	newStore := func() *store {
		b, _ := betesting.NewDefaultTmpBackend(t)
		s := NewStore(zaptest.NewLogger(t), b, &lease.FakeLessor{}, StoreConfig{})
		t.Cleanup(func() { cleanup(s, b) })
		return s
	}
	compact := func(s *store, rev int64) {
		done, err := s.Compact(traceutil.TODO(), rev)
		require.NoError(t, err)
		<-done
	}

	leader, follower := newStore(), newStore()
	for _, s := range []*store{leader, follower} {
		s.Put([]byte("foo"), []byte("bar"), lease.NoLease) // rev 2
		compact(s, 2)
		s.DeleteRange([]byte("foo"), nil) // rev 3: no key is left
	}

	compact(leader, 3)
	stored := leader.HashStorage().Hashes()
	require.NotEmpty(t, stored)
	leaderHash := stored[len(stored)-1]
	require.Equal(t, int64(3), leaderHash.Revision)

	followerHash, _, err := follower.HashStorage().HashByRev(3)
	require.NoError(t, err)
	require.Equal(t, leaderHash.CompactRevision, followerHash.CompactRevision)
	assert.Equal(t, leaderHash.Hash, followerHash.Hash,
		"same revision and compact revision should give the same hash")
}
