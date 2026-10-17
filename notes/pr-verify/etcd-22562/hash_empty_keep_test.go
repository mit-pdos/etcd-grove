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

	"github.com/stretchr/testify/require"
	"go.uber.org/zap/zaptest"

	"go.etcd.io/etcd/pkg/v3/traceutil"
	"go.etcd.io/etcd/server/v3/lease"
	betesting "go.etcd.io/etcd/server/v3/storage/backend/testing"
)

// TestHashByRevEmptyKeepMatchesCompactionHash: a key put at 2, the store
// compacted at 2, the key deleted at 3. Keep(3) is empty (the tombstone at 3
// ends a generation), Compact(3) keeps the tombstone. The hash of revision 3
// with compaction revision 2 computed by HashByRev before compacting at 3 must
// equal the one the compaction at 3 computes and stores (same revision, same
// compaction revision). Before etcd-io/etcd#22562 the first hashes the put at
// 2 and the second does not.
func TestHashByRevEmptyKeepMatchesCompactionHash(t *testing.T) {
	b, _ := betesting.NewDefaultTmpBackend(t)
	s := NewStore(zaptest.NewLogger(t), b, &lease.FakeLessor{}, StoreConfig{})
	defer cleanup(s, b)

	s.Put([]byte("k"), []byte("v"), 0) // rev 2
	done, err := s.Compact(traceutil.TODO(), 2)
	require.NoError(t, err)
	<-done
	s.DeleteRange([]byte("k"), nil) // rev 3

	before, _, err := s.HashStorage().HashByRev(3)
	require.NoError(t, err)
	require.Equal(t, int64(2), before.CompactRevision)

	done, err = s.Compact(traceutil.TODO(), 3)
	require.NoError(t, err)
	<-done
	stored := s.HashStorage().Hashes()
	require.NotEmpty(t, stored)
	compacted := stored[len(stored)-1]
	require.Equal(t, int64(3), compacted.Revision)
	require.Equal(t, int64(2), compacted.CompactRevision)

	require.Equal(t, compacted, before, "HashByRev(3) before compaction differs from the compaction's hash of revision 3")
}
