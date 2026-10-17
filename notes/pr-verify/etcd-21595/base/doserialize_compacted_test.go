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
	"context"
	"encoding/base64"
	"sync"
	"testing"
	"time"

	"github.com/stretchr/testify/require"
	"go.uber.org/zap/zaptest"
	"golang.org/x/crypto/bcrypt"
	"google.golang.org/grpc/metadata"

	"go.etcd.io/etcd/api/v3/authpb"
	pb "go.etcd.io/etcd/api/v3/etcdserverpb"
	"go.etcd.io/etcd/api/v3/v3rpc/rpctypes"
	"go.etcd.io/etcd/server/v3/auth"
	"go.etcd.io/etcd/server/v3/config"
	betesting "go.etcd.io/etcd/server/v3/storage/backend/testing"
	"go.etcd.io/etcd/server/v3/storage/mvcc"
	"go.etcd.io/etcd/server/v3/storage/schema"
)

// TestDoSerializeCompactedNotMaskedByAuthRevision: a serialized read whose
// fetch fails (ErrCompacted) while an auth change commits concurrently. The
// read's error must reach the caller, not ErrAuthOldRevision.
func TestDoSerializeCompactedNotMaskedByAuthRevision(t *testing.T) {
	lg := zaptest.NewLogger(t)
	be, _ := betesting.NewDefaultTmpBackend(t)
	defer betesting.Close(t, be)

	waiter := func(uint64) <-chan struct{} { ch := make(chan struct{}); close(ch); return ch }
	tp, err := auth.NewTokenProvider(lg, "simple", waiter, 5*time.Minute)
	require.NoError(t, err)
	as := auth.NewAuthStore(lg, schema.NewAuthBackend(lg, be), tp, bcrypt.MinCost)
	defer as.Close()

	hp, _ := bcrypt.GenerateFromPassword([]byte("root"), bcrypt.MinCost)
	_, err = as.UserAdd(&pb.AuthUserAddRequest{Name: "root", HashedPassword: base64.StdEncoding.EncodeToString(hp), Options: &authpb.UserAddOptions{}})
	require.NoError(t, err)
	_, err = as.RoleAdd(&pb.AuthRoleAddRequest{Name: "root"})
	require.NoError(t, err)
	_, err = as.UserGrantRole(&pb.AuthUserGrantRoleRequest{User: "root", Role: "root"})
	require.NoError(t, err)
	require.NoError(t, as.AuthEnable())

	actx := context.WithValue(context.WithValue(t.Context(), auth.AuthenticateParamIndex{}, uint64(1)), auth.AuthenticateParamSimpleTokenPrefix{}, "probe")
	ar, err := as.Authenticate(actx, "root", "root")
	require.NoError(t, err)

	srv := &EtcdServer{
		lgMu:      new(sync.RWMutex),
		lg:        lg,
		Cfg:       config.ServerConfig{Logger: lg},
		authStore: as,
	}
	ctx := metadata.NewIncomingContext(t.Context(), metadata.Pairs(rpctypes.TokenFieldNameGRPC, ar.Token))

	chk := func(*auth.AuthInfo) error { return nil }
	var getErr error
	get := func() {
		// an auth change commits while the read is served ...
		_, aerr := as.RoleAdd(&pb.AuthRoleAddRequest{Name: "concurrent"})
		require.NoError(t, aerr)
		// ... and the read fails
		getErr = mvcc.ErrCompacted
	}

	serr := srv.doSerialize(ctx, chk, get)
	t.Logf("doSerialize returned %v (get's error: %v)", serr, getErr)
	require.ErrorIs(t, serr, mvcc.ErrCompacted)
}
