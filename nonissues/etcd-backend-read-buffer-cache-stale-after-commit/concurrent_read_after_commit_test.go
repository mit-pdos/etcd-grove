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

package backend_test

import (
	"testing"
	"time"

	"github.com/stretchr/testify/require"

	betesting "go.etcd.io/etcd/server/v3/storage/backend/testing"
	"go.etcd.io/etcd/server/v3/storage/schema"
)

// TestConcurrentReadTxAfterCommit ensures that a commit does not change what a
// concurrent read transaction reads.
func TestConcurrentReadTxAfterCommit(t *testing.T) {
	b, _ := betesting.NewTmpBackend(t, time.Hour, 10000)
	defer betesting.Close(t, b)

	tx := b.BatchTx()
	tx.Lock()
	tx.UnsafeCreateBucket(schema.Key)
	tx.UnsafePut(schema.Key, []byte("abc"), []byte("ABC"))
	tx.Unlock()

	rangeKeys := func() []string {
		rtx := b.ConcurrentReadTx()
		rtx.RLock()
		defer rtx.RUnlock()
		ks, _ := rtx.UnsafeRange(schema.Key, []byte("abc"), []byte("\xff"), 0)
		var keys []string
		for _, k := range ks {
			keys = append(keys, string(k))
		}
		return keys
	}
	require.Equal(t, []string{"abc"}, rangeKeys(), "before commit")
	b.ForceCommit()
	require.Equal(t, []string{"abc"}, rangeKeys(), "after commit")
}
