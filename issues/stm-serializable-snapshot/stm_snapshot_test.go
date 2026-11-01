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

package concurrency_test

import (
	"context"
	"testing"

	"github.com/stretchr/testify/require"

	clientv3 "go.etcd.io/etcd/client/v3"
	"go.etcd.io/etcd/client/v3/concurrency"
	"go.etcd.io/etcd/tests/v3/framework/integration"
)

// TestSTMSerializableSnapshotAfterConflict checks the documented promise of
// the serializable isolation levels: "reads within the same transaction
// attempt return data from the revision of the first read".
//
// x and y are only ever written together (to "1"/"1", then "2"/"2"). The
// first attempt reads y and writes z; y is changed behind its back, so its
// commit fails, and the commit's Else branch prefetches y (at the failed
// commit's revision). Before the second attempt's first read, x and y are
// changed together. The second attempt then reads x first (not prefetched:
// a fresh read at the latest revision, which sets the attempt's snapshot),
// then y (prefetched: the value from before the change). It sees x and y
// from different revisions, a state that never existed.
func TestSTMSerializableSnapshotAfterConflict(t *testing.T) {
	t.Run("SerializableSnapshot", func(t *testing.T) {
		testSTMSnapshotAfterConflict(t, concurrency.SerializableSnapshot, "/snap-ss/")
	})
	t.Run("Serializable", func(t *testing.T) {
		testSTMSnapshotAfterConflict(t, concurrency.Serializable, "/snap-s/")
	})
}

func testSTMSnapshotAfterConflict(t *testing.T, iso concurrency.Isolation, pfx string) {
	cli, err := integration.NewClient(t, clientv3.Config{Endpoints: exampleEndpoints()})
	require.NoError(t, err)
	defer cli.Close()
	ctx := context.Background()

	put := func(x, y string) {
		_, err := cli.Txn(ctx).Then(clientv3.OpPut(pfx+"x", x), clientv3.OpPut(pfx+"y", y)).Commit()
		require.NoError(t, err)
	}
	put("0", "0")

	attempt := 0
	var seen [][2]string
	apply := func(s concurrency.STM) error {
		attempt++
		switch attempt {
		case 1:
			s.Get(pfx + "y")
			s.Put(pfx+"z", "1")
			put("1", "1") // y changes: this attempt's commit fails
		case 2:
			put("2", "2") // x and y change together, after the prefetch of y
			x := s.Get(pfx + "x")
			y := s.Get(pfx + "y")
			seen = append(seen, [2]string{x, y})
			s.Put(pfx+"z", "2")
		default:
			x := s.Get(pfx + "x")
			y := s.Get(pfx + "y")
			seen = append(seen, [2]string{x, y})
			s.Put(pfx+"z", "3")
		}
		return nil
	}
	_, err = concurrency.NewSTM(cli, apply, concurrency.WithIsolation(iso))
	require.NoError(t, err)
	for i, xy := range seen {
		t.Logf("isolation %d, attempt %d read x=%s y=%s", iso, i+2, xy[0], xy[1])
	}
	for _, xy := range seen {
		require.Equalf(t, xy[0], xy[1],
			"isolation %d: an attempt read x=%s and y=%s, written together only with equal values", iso, xy[0], xy[1])
	}
}
