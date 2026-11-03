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

package clientv3test

import (
	"context"
	"testing"
	"time"

	"github.com/stretchr/testify/require"

	"go.etcd.io/etcd/api/v3/mvccpb"
	clientv3 "go.etcd.io/etcd/client/v3"
	"go.etcd.io/etcd/tests/v3/framework/integration"
)

// TestWatchFromCompactRevAfterSiblingPutDelete ensures that a watch from the
// compaction revision sees the same events of that revision as before the
// compaction. The revision is a txn that puts a key in one nested txn and
// deletes it in a later sibling, which the server accepts.
func TestWatchFromCompactRevAfterSiblingPutDelete(t *testing.T) {
	integration.BeforeTest(t)

	clus := integration.NewCluster(t, &integration.ClusterConfig{Size: 1})
	defer clus.Terminate(t)

	cli := clus.RandClient()
	ctx := t.Context()

	_, err := cli.Put(ctx, "a", "v1")
	require.NoError(t, err)
	put := clientv3.OpTxn(nil, []clientv3.Op{clientv3.OpPut("a", "v2")}, nil)
	del := clientv3.OpTxn(nil, []clientv3.Op{clientv3.OpDelete("a")}, nil)
	resp, err := cli.Txn(ctx).Then(put, del).Commit()
	require.NoError(t, err)
	rev := resp.Header.Revision

	events := func() []mvccpb.Event_EventType {
		wctx, cancel := context.WithTimeout(ctx, 5*time.Second)
		defer cancel()
		wr := <-cli.Watch(wctx, "a", clientv3.WithRev(rev))
		require.NoError(t, wr.Err())
		var types []mvccpb.Event_EventType
		for _, ev := range wr.Events {
			types = append(types, ev.Type)
		}
		return types
	}

	before := events()
	_, err = cli.Compact(ctx, rev, clientv3.WithCompactPhysical())
	require.NoError(t, err)
	after := events()
	require.Equalf(t, before, after, "events of revision %d for a watch from it, before and after compacting at it", rev)
}
