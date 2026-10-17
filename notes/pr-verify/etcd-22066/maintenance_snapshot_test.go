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

package v3rpc

import (
	"crypto/sha256"
	"errors"
	"io"
	"testing"

	"github.com/stretchr/testify/require"
	"go.uber.org/zap/zaptest"
	"google.golang.org/grpc"

	pb "go.etcd.io/etcd/api/v3/etcdserverpb"
	"go.etcd.io/etcd/client/pkg/v3/types"
	"go.etcd.io/etcd/server/v3/etcdserver/apply"
	"go.etcd.io/etcd/server/v3/storage/backend"
	betesting "go.etcd.io/etcd/server/v3/storage/backend/testing"
	"go.etcd.io/etcd/server/v3/storage/schema"
)

type snapStatus struct{ apply.RaftStatusGetter }

func (snapStatus) Term() uint64       { return 1 }
func (snapStatus) Leader() types.ID   { return 1 }
func (snapStatus) MemberID() types.ID { return 1 }

type snapBackendGetter struct{ be backend.Backend }

func (g snapBackendGetter) Backend() backend.Backend { return g.be }

// failingSnapBackend is a backend whose snapshots fail after writing `limit` bytes,
// as a read error of the database file would.
type failingSnapBackend struct {
	backend.Backend
	limit int64
}

func (b failingSnapBackend) Snapshot() backend.Snapshot {
	return failingSnapshot{b.Backend.Snapshot(), b.limit}
}

type failingSnapshot struct {
	backend.Snapshot
	limit int64
}

func (s failingSnapshot) WriteTo(w io.Writer) (int64, error) {
	pr, pw := io.Pipe()
	go func() { s.Snapshot.WriteTo(pw); pw.Close() }()
	n, _ := io.CopyN(w, pr, s.limit)
	pr.Close()
	return n, errors.New("injected read error")
}

// recordingSnapshotServer records the responses; it fails the stream after maxSends,
// as a client that gives up would.
type recordingSnapshotServer struct {
	grpc.ServerStream
	resps    []*pb.SnapshotResponse
	maxSends int
	tooMany  bool // a Send was refused
}

var errTooManySends = errors.New("too many responses")

func (s *recordingSnapshotServer) Send(r *pb.SnapshotResponse) error {
	if len(s.resps) >= s.maxSends {
		s.tooMany = true
		return errTooManySends
	}
	s.resps = append(s.resps, r)
	return nil
}

func lastResp(rs []*pb.SnapshotResponse) *pb.SnapshotResponse {
	if len(rs) == 0 {
		return nil
	}
	return rs[len(rs)-1]
}

func newTestMaintenanceServer(t *testing.T, be backend.Backend) *maintenanceServer {
	return &maintenanceServer{
		lg:  zaptest.NewLogger(t),
		bg:  snapBackendGetter{be},
		hdr: header{clusterID: 1, memberID: 1, sg: snapStatus{}},
	}
}

// TestSnapshotStream checks the responses of a whole snapshot of a database of
// several send buffers: they carry the database then its 32-byte SHA-256, each
// response's RemainingBytes is the number of bytes sent after it (the SHA-256
// included), and the stream ends after the SHA-256.
func TestSnapshotStream(t *testing.T) {
	be, _ := betesting.NewDefaultTmpBackend(t)
	defer betesting.Close(t, be)
	tx := be.BatchTx()
	tx.Lock()
	tx.UnsafeCreateBucket(schema.Test)
	for i := 0; i < 100; i++ {
		tx.UnsafePut(schema.Test, []byte{byte(i)}, make([]byte, 1024))
	}
	tx.Unlock()
	be.ForceCommit()
	ms := newTestMaintenanceServer(t, be)
	snap := be.Snapshot()
	dbSize := snap.Size()
	require.NoError(t, snap.Close())

	srv := &recordingSnapshotServer{maxSends: 1000}
	err := ms.Snapshot(&pb.SnapshotRequest{}, srv)
	require.NoErrorf(t, err, "after %d responses, the last %+v", len(srv.resps), lastResp(srv.resps))

	var all int64
	for _, r := range srv.resps {
		all += int64(len(r.Blob))
	}
	require.Equal(t, dbSize+sha256.Size, all)
	require.Greater(t, len(srv.resps), 2, "several data responses")
	// etcd#22066's e2e test checks len(Blob)+RemainingBytes == dbSize+32 for every
	// data response: true of the first only.
	for i, r := range srv.resps[:len(srv.resps)-1] {
		t.Logf("response %d: len(Blob)+RemainingBytes = %d (dbSize+32 = %d)",
			i, int64(len(r.Blob))+int64(r.RemainingBytes), all)
	}
	var sent int64
	for i, r := range srv.resps {
		sent += int64(len(r.Blob))
		require.Equalf(t, uint64(all-sent), r.RemainingBytes, "response %d of %d", i, len(srv.resps))
	}
	last := srv.resps[len(srv.resps)-1]
	require.Len(t, last.Blob, sha256.Size)
}

// TestSnapshotWriteToError checks that a snapshot whose WriteTo fails part way
// ends the stream with an error, rather than sending empty responses until the
// client gives up.
func TestSnapshotWriteToError(t *testing.T) {
	be, _ := betesting.NewDefaultTmpBackend(t)
	defer betesting.Close(t, be)
	ms := newTestMaintenanceServer(t, failingSnapBackend{be, 4096})

	srv := &recordingSnapshotServer{maxSends: 1000}
	err := ms.Snapshot(&pb.SnapshotRequest{}, srv)
	require.Error(t, err)
	require.Falsef(t, srv.tooMany, "the server kept sending: %d responses, the last %+v",
		len(srv.resps), lastResp(srv.resps))
}
