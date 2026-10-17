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
	"crypto/sha256"
	"errors"
	"io"
	"testing"
	"time"

	"github.com/stretchr/testify/require"

	pb "go.etcd.io/etcd/api/v3/etcdserverpb"
	"go.etcd.io/etcd/tests/v3/framework/integration"
)

// TestMaintenanceSnapshotStreamTerminates reads a snapshot stream response by
// response and checks that it ends: the server sends the database in at most
// ceil(size/32KiB)+1 data responses, then one 32-byte SHA-256 response with
// RemainingBytes 0, then closes the stream; the bytes received add up to the
// database size plus 32, and each response's RemainingBytes is what is left of
// that total after it.
func TestMaintenanceSnapshotStreamTerminates(t *testing.T) {
	integration.BeforeTest(t)

	clus := integration.NewCluster(t, &integration.ClusterConfig{Size: 1})
	defer clus.Terminate(t)

	mc := pb.NewMaintenanceClient(clus.Client(0).ActiveConnection())
	ctx, cancel := context.WithTimeout(t.Context(), 10*time.Second)
	defer cancel()
	stream, err := mc.Snapshot(ctx, &pb.SnapshotRequest{})
	require.NoError(t, err)

	var resps []*pb.SnapshotResponse
	var received int64
	var first *pb.SnapshotResponse
	for {
		resp, err := stream.Recv()
		if errors.Is(err, io.EOF) {
			break
		}
		require.NoErrorf(t, err, "after %d responses (%d bytes); the last ones: %v",
			len(resps), received, tail(resps))
		if first == nil {
			first = resp
		}
		received += int64(len(resp.Blob))
		resps = append(resps, resp)
	}
	require.NotEmpty(t, resps)
	total := int64(len(first.Blob)) + int64(first.RemainingBytes)
	require.Equal(t, total, received, "bytes received vs. first response's len(Blob)+RemainingBytes")
	var sent int64
	for i, r := range resps {
		sent += int64(len(r.Blob))
		require.Equalf(t, uint64(total-sent), r.RemainingBytes, "response %d", i)
	}
	last := resps[len(resps)-1]
	require.Len(t, last.Blob, sha256.Size)
	require.Zero(t, last.RemainingBytes)
	dbSize := received - sha256.Size
	require.LessOrEqual(t, int64(len(resps)), (dbSize+32*1024-1)/(32*1024)+2)
}

func tail(rs []*pb.SnapshotResponse) []string {
	var out []string
	for i := max(0, len(rs)-3); i < len(rs); i++ {
		out = append(out, "{len(Blob)="+itoa(len(rs[i].Blob))+" RemainingBytes="+itoa(int(rs[i].RemainingBytes))+"}")
	}
	return out
}

func itoa(n int) string {
	if n == 0 {
		return "0"
	}
	s := ""
	for ; n > 0; n /= 10 {
		s = string(rune('0'+n%10)) + s
	}
	return s
}
