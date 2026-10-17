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

	"go.uber.org/zap/zaptest"

	"go.etcd.io/etcd/server/v3/lease"
	betesting "go.etcd.io/etcd/server/v3/storage/backend/testing"
)

// HashByRev (HashKV's) with a negative revision is not refused: it returns the hash of no
// revision at all, with HashRevision set to the negative value and no error, where 0 means
// the current revision and a revision above it is ErrFutureRev.
func TestHashByRevNegativeRevision(t *testing.T) {
	b, _ := betesting.NewDefaultTmpBackend(t)
	s := NewStore(zaptest.NewLogger(t), b, &lease.FakeLessor{}, StoreConfig{})
	defer cleanup(s, b)
	for i := 2; i <= 10; i++ {
		s.Put([]byte("foo"), []byte(fmt.Sprintf("v%d", i)), lease.NoLease)
	}
	h, cur, err := s.HashStorage().HashByRev(-5)
	t.Logf("HashByRev(-5) = %+v, current revision %d, err %v", h, cur, err)
	if err == nil {
		t.Errorf("HashByRev(-5): no error, hash %+v (current revision %d)", h, cur)
	}
}
