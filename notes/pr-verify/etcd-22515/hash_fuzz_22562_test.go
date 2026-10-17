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

// FuzzCompactionHash copied verbatim from etcd-io/etcd#22562 (e35b5916f,
// server/storage/mvcc/hash_test.go), to run against other revisions (it uses
// hashTestCase from hash_test.go).

package mvcc

import (
	"testing"

	"github.com/stretchr/testify/require"
	"go.uber.org/zap/zaptest"

	"go.etcd.io/etcd/server/v3/lease"
	betesting "go.etcd.io/etcd/server/v3/storage/backend/testing"
)

func FuzzCompactionHash(f *testing.F) {
	f.Add([]byte{}, uint8(1))
	f.Add([]byte{0, 0, 128, 0, 64, 128, 64}, uint8(1))
	operations := make([]byte, 256)
	for i := range operations {
		operations[i] = byte(i % 64)
	}
	f.Add(operations, uint8(16))
	f.Fuzz(func(t *testing.T, operations []byte, batchLimit uint8) {
		if len(operations) > 4096 {
			t.Skip()
		}
		b, _ := betesting.NewDefaultTmpBackend(t)
		s := NewStore(zaptest.NewLogger(t), b, &lease.FakeLessor{}, StoreConfig{
			CompactionBatchLimit: int(batchLimit)%32 + 1,
		})
		defer cleanup(s, b)

		tc := hashTestCase{s}
		ctx := t.Context()
		lastCompactRev := s.Rev()
		for i, operation := range operations {
			key := []byte{operation & 15}
			if operation&128 != 0 {
				s.DeleteRange(key, nil)
			} else {
				s.Put(key, []byte{operation}, 0)
			}
			if operation&64 == 0 && i != len(operations)-1 {
				continue
			}
			if s.Rev() == lastCompactRev {
				continue
			}
			rev := lastCompactRev + 1 + int64(operation)%(s.Rev()-lastCompactRev)
			before, err := tc.HashByRev(ctx, rev)
			require.NoError(t, err)
			require.NoError(t, tc.Compact(ctx, rev))
			require.NoError(t, tc.Defrag(ctx))
			after, err := tc.HashByRev(ctx, rev)
			require.NoError(t, err)
			require.Equal(t, before, after, "hash changed at revision %d", rev)
			lastCompactRev = rev
		}
	})
}


