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

package etcdserver

import (
	"bytes"
	"io"
	"net/http"
	"net/http/httptest"
	"strconv"
	"strings"
	"testing"

	"go.uber.org/zap"

	"go.etcd.io/etcd/client/pkg/v3/types"
	"go.etcd.io/etcd/server/v3/lease"
	betesting "go.etcd.io/etcd/server/v3/storage/backend/testing"
	"go.etcd.io/etcd/server/v3/storage/mvcc"
)

// countingBody is a request body of size bytes (a HashKVRequest padded with
// an unknown field) that counts how many bytes the handler reads from it.
type countingBody struct {
	r    io.Reader
	read int
}

func newCountingBody(size int) *countingBody {
	prefix := `{"revision":1,"padding":"`
	suffix := `"}`
	pad := size - len(prefix) - len(suffix)
	if pad < 0 {
		pad = 0
	}
	return &countingBody{r: strings.NewReader(prefix + strings.Repeat("a", pad) + suffix)}
}

func (b *countingBody) Read(p []byte) (int, error) {
	n, err := b.r.Read(p)
	b.read += n
	return n, err
}

func (b *countingBody) Close() error { return nil }

func newBoundTestHandler(t *testing.T) (*hashKVHandler, int) {
	localClusterID := 111196
	etcdSrv := &EtcdServer{}
	etcdSrv.cluster = newTestCluster(t)
	etcdSrv.cluster.SetID(types.ID(localClusterID), types.ID(localClusterID))
	be, _ := betesting.NewDefaultTmpBackend(t)
	t.Cleanup(func() { betesting.Close(t, be) })
	etcdSrv.kv = mvcc.New(zap.NewNop(), be, &lease.FakeLessor{}, mvcc.StoreConfig{})
	t.Cleanup(func() { etcdSrv.kv.Close() })
	return &hashKVHandler{lg: zap.NewNop(), server: etcdSrv}, localClusterID
}

// TestHashKVHandlerBodyBound checks the bound at its edge (a body of exactly
// 64 KiB is served, one byte more is rejected with 413) and how much of a
// large body the handler reads: at most 64 KiB + 1 bytes with the bound
// (PR head), all of it without (the base).
func TestHashKVHandlerBodyBound(t *testing.T) {
	const limit = 64 * 1024
	for _, tc := range []struct {
		name string
		size int
	}{
		{"exactly the limit", limit},
		{"one byte over", limit + 1},
		{"16 MiB", 16 << 20},
	} {
		t.Run(tc.name, func(t *testing.T) {
			ph, cid := newBoundTestHandler(t)
			body := newCountingBody(tc.size)
			req := httptest.NewRequest(http.MethodGet, PeerHashKVPath, nil)
			req.Body = body
			req.Header.Set("X-Etcd-Cluster-ID", strconv.FormatUint(uint64(cid), 16))
			rec := httptest.NewRecorder()
			ph.ServeHTTP(rec, req)
			t.Logf("body %d bytes: status %d, read %d bytes", tc.size, rec.Code, body.read)
			if tc.size <= limit && rec.Code != http.StatusOK {
				t.Errorf("status %d, want 200 (%s)", rec.Code, bytes.TrimSpace(rec.Body.Bytes()))
			}
			if tc.size > limit && rec.Code != http.StatusRequestEntityTooLarge {
				t.Errorf("status %d, want 413", rec.Code)
			}
			if body.read > limit+1 {
				t.Errorf("read %d bytes of the body, want at most %d", body.read, limit+1)
			}
		})
	}
}
