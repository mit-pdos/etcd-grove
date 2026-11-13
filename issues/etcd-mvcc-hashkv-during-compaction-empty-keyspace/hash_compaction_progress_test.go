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
	"time"

	"github.com/stretchr/testify/assert"
	"github.com/stretchr/testify/require"
	"go.uber.org/zap/zaptest"

	"go.etcd.io/etcd/pkg/v3/traceutil"
	"go.etcd.io/etcd/server/v3/lease"
	betesting "go.etcd.io/etcd/server/v3/storage/backend/testing"
)

// Two members that have both applied the same compaction, one of which is
// still removing the compacted revisions batch by batch. PeriodicCheck
// compares their HashByRev at the latest revision.
func TestHashByRevIndependentOfCompactionProgressWhenKeyspaceEmpty(t *testing.T) {
	newStore := func(cfg StoreConfig) *store {
		b, _ := betesting.NewDefaultTmpBackend(t)
		s := NewStore(zaptest.NewLogger(t), b, &lease.FakeLessor{}, cfg)
		t.Cleanup(func() { cleanup(s, b) })
		return s
	}

	finished := newStore(StoreConfig{})
	// One revision per batch, and an hour between batches.
	running := newStore(StoreConfig{CompactionBatchLimit: 1, CompactionSleepInterval: time.Hour})
	for _, s := range []*store{finished, running} {
		s.Put([]byte("a"), []byte("1"), lease.NoLease) // rev 2, kept by the compaction at 4
		s.Put([]byte("b"), []byte("1"), lease.NoLease) // rev 3, removed by the compaction at 4
		s.Put([]byte("b"), []byte("2"), lease.NoLease) // rev 4
		s.DeleteRange([]byte("a"), nil)                // rev 5
		s.DeleteRange([]byte("b"), nil)                // rev 6: no key is left
	}

	done, err := finished.Compact(traceutil.TODO(), 4)
	require.NoError(t, err)
	<-done
	// The first batch holds only revision 2, which is kept; revision 3 stays
	// until the next batch, an hour later.
	_, err = running.Compact(traceutil.TODO(), 4)
	require.NoError(t, err)

	h1, _, err := finished.HashStorage().HashByRev(0)
	require.NoError(t, err)
	h2, _, err := running.HashStorage().HashByRev(0)
	require.NoError(t, err)
	require.Equal(t, h1.Revision, h2.Revision)
	require.Equal(t, h1.CompactRevision, h2.CompactRevision)
	assert.Equal(t, h1.Hash, h2.Hash,
		"same revision and compact revision should give the same hash")
}
