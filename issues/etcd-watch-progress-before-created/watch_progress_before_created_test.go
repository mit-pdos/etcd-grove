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

package watch

import (
	"bytes"
	"context"
	"testing"
	"time"

	"github.com/stretchr/testify/require"

	pb "go.etcd.io/etcd/api/v3/etcdserverpb"
	clientv3 "go.etcd.io/etcd/client/v3"
	"go.etcd.io/etcd/tests/v3/framework/integration"
)

// TestV3WatchProgressBeforeCreated ensures that the progress response to a
// request received before a watcher was created does not arrive between that
// watcher's created response and its events.
func TestV3WatchProgressBeforeCreated(t *testing.T) {
	if integration.ThroughProxy {
		t.Skip("grpc proxy currently does not support requesting progress notifications")
	}
	integration.BeforeTest(t)
	clus := integration.NewCluster(t, &integration.ClusterConfig{Size: 1})
	defer clus.Terminate(t)

	ctx, cancel := context.WithTimeout(t.Context(), 30*time.Second)
	defer cancel()
	wStream, err := integration.ToGRPC(clus.RandClient()).Watch.Watch(ctx)
	require.NoError(t, err)
	kvc := integration.ToGRPC(clus.RandClient()).KV

	presp, err := kvc.Put(ctx, &pb.PutRequest{Key: []byte("b"), Value: []byte("1")})
	require.NoError(t, err)
	bRev := presp.Header.Revision
	require.NoError(t, wStream.Send(&pb.WatchRequest{RequestUnion: &pb.WatchRequest_CreateRequest{
		CreateRequest: &pb.WatchCreateRequest{Key: []byte("a")},
	}}))
	wresp, err := wStream.Recv()
	require.NoError(t, err)
	require.True(t, wresp.Created)

	// events too large for the stream's flow control window keep the server's
	// responses queued until the stream is read
	value := bytes.Repeat([]byte("x"), 100*1024)
	for i := 0; i < 10; i++ {
		_, err = kvc.Put(ctx, &pb.PutRequest{Key: []byte("a"), Value: value})
		require.NoError(t, err)
	}
	require.NoError(t, wStream.Send(&pb.WatchRequest{RequestUnion: &pb.WatchRequest_ProgressRequest{
		ProgressRequest: &pb.WatchProgressRequest{},
	}}))
	require.NoError(t, wStream.Send(&pb.WatchRequest{RequestUnion: &pb.WatchRequest_CreateRequest{
		CreateRequest: &pb.WatchCreateRequest{Key: []byte("b"), StartRevision: bRev},
	}}))
	require.Eventuallyf(t, func() bool {
		watchers, merr := clus.Members[0].Metric("etcd_debugging_mvcc_watcher_total")
		return merr == nil && watchers == "2"
	}, 10*time.Second, 10*time.Millisecond, "watcher on b not created")

	created, progress := false, false
	for {
		wresp, err = wStream.Recv()
		require.NoError(t, err)
		if len(wresp.Events) > 0 && string(wresp.Events[0].Kv.Key) == "b" {
			break
		}
		if wresp.Created {
			created = true
		}
		if wresp.WatchId == clientv3.InvalidWatchID {
			progress = true
			require.Falsef(t, created, "progress response at revision %d after the created response of the watcher on b, before its event at revision %d", wresp.Header.Revision, bRev)
		}
	}
	require.Truef(t, progress, "no progress response")
}
