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
	"go.etcd.io/etcd/tests/v3/framework/integration"
)

// TestV3WatchReuseCanceledID ensures that a watcher created with the ID of a
// canceled watcher receives no events of the canceled watcher.
func TestV3WatchReuseCanceledID(t *testing.T) {
	if integration.ThroughProxy {
		t.Skip("grpc proxy does not keep the client's watch ID")
	}
	integration.BeforeTest(t)
	clus := integration.NewCluster(t, &integration.ClusterConfig{Size: 1})
	defer clus.Terminate(t)

	ctx, cancel := context.WithTimeout(t.Context(), 30*time.Second)
	defer cancel()
	wStream, err := integration.ToGRPC(clus.RandClient()).Watch.Watch(ctx)
	require.NoError(t, err)
	kvc := integration.ToGRPC(clus.RandClient()).KV

	require.NoError(t, wStream.Send(&pb.WatchRequest{RequestUnion: &pb.WatchRequest_CreateRequest{
		CreateRequest: &pb.WatchCreateRequest{Key: []byte("a"), WatchId: 1},
	}}))
	wresp, err := wStream.Recv()
	require.NoError(t, err)
	require.True(t, wresp.Created)

	// watcher 1 is canceled while its events on "a" are queued at the
	// server: the stream is not read until watcher 1 is created again
	var presp *pb.PutResponse
	value := bytes.Repeat([]byte("x"), 50*1024)
	for i := 0; i < 20; i++ {
		presp, err = kvc.Put(ctx, &pb.PutRequest{Key: []byte("a"), Value: value})
		require.NoError(t, err)
	}
	require.NoError(t, wStream.Send(&pb.WatchRequest{RequestUnion: &pb.WatchRequest_CancelRequest{
		CancelRequest: &pb.WatchCancelRequest{WatchId: 1},
	}}))
	require.Eventuallyf(t, func() bool {
		watchers, merr := clus.Members[0].Metric("etcd_debugging_mvcc_watcher_total")
		return merr == nil && watchers == "0"
	}, 10*time.Second, 10*time.Millisecond, "watcher 1 not canceled")
	require.NoError(t, wStream.Send(&pb.WatchRequest{RequestUnion: &pb.WatchRequest_CreateRequest{
		CreateRequest: &pb.WatchCreateRequest{Key: []byte("b"), StartRevision: presp.Header.Revision + 1, WatchId: 1},
	}}))
	_, err = kvc.Put(ctx, &pb.PutRequest{Key: []byte("b"), Value: []byte("1")})
	require.NoError(t, err)

	recreated := false
	var keys []string
	for len(keys) == 0 || keys[len(keys)-1] != "b" {
		wresp, err = wStream.Recv()
		require.NoError(t, err)
		recreated = recreated || wresp.Created
		for _, ev := range wresp.Events {
			if recreated {
				keys = append(keys, string(ev.Kv.Key))
			}
		}
	}
	require.Equalf(t, []string{"b"}, keys, "events received after watcher 1 was created on b")
}
