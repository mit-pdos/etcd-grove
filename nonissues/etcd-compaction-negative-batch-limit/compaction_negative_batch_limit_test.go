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
	"fmt"
	"testing"
	"time"

	"go.uber.org/zap/zaptest"

	"go.etcd.io/etcd/pkg/v3/traceutil"
	"go.etcd.io/etcd/server/v3/lease"
	betesting "go.etcd.io/etcd/server/v3/storage/backend/testing"
)

// TestCompactionNegativeBatchLimit ensures that a compaction finishes whatever
// --compaction-batch-limit is set to (the flag is passed to StoreConfig as is).
func TestCompactionNegativeBatchLimit(t *testing.T) {
	for _, limit := range []int{0, 1, -1} {
		t.Run(fmt.Sprintf("limit=%d", limit), func(t *testing.T) {
			b, _ := betesting.NewDefaultTmpBackend(t)
			s := NewStore(zaptest.NewLogger(t), b, &lease.FakeLessor{},
				StoreConfig{CompactionBatchLimit: limit, CompactionSleepInterval: time.Millisecond})
			defer func() { s.Close(); b.Close() }()
			for i := 0; i < 5; i++ {
				s.Put([]byte("foo"), []byte(fmt.Sprint(i)), lease.NoLease)
			}
			ch, err := s.Compact(traceutil.TODO(), 4)
			if err != nil {
				t.Fatal(err)
			}
			select {
			case <-ch:
			case <-time.After(5 * time.Second):
				t.Fatalf("compaction with batch limit %d still running after 5s", limit)
			}
		})
	}
}
