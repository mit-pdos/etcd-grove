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

package auth

// Probes of etcd-io/etcd#22560's AuthStore.RenewToken (run against the PR head 7a87a72d1):
// what renewal accepts, compared with what the token providers' own checks (expiry, the
// auth revision) accept.

import (
	"context"
	"fmt"
	"testing"
	"time"

	"github.com/stretchr/testify/require"
	"go.uber.org/zap/zaptest"
	"golang.org/x/crypto/bcrypt"
	"google.golang.org/grpc/metadata"

	"go.etcd.io/etcd/api/v3/authpb"
	pb "go.etcd.io/etcd/api/v3/etcdserverpb"
	"go.etcd.io/etcd/api/v3/v3rpc/rpctypes"
)

func tokenCtx(t *testing.T, token string) context.Context {
	return metadata.NewIncomingContext(t.Context(), metadata.Pairs(rpctypes.TokenFieldNameGRPC, token))
}

func newJWTStoreTTL(t *testing.T, ttl string) *authStore {
	opts := fmt.Sprintf("%s,ttl=%s", testJWTOpts(), ttl)
	tp, err := NewTokenProvider(zaptest.NewLogger(t), opts, dummyIndexWaiter, simpleTokenTTLDefault)
	require.NoError(t, err)
	as := NewAuthStore(zaptest.NewLogger(t), newBackendMock(), tp, bcrypt.MinCost)
	t.Cleanup(func() { as.Close() })
	require.NoError(t, enableAuthAndCreateRoot(as))
	return as.(*authStore)
}

// A simple token that the TTL keeper has expired (it no longer authenticates) is brought
// back by RenewToken: the TTL no longer bounds how long a simple token can be used.
func TestRenewTokenResurrectsExpiredSimpleToken(t *testing.T) {
	tp, err := NewTokenProvider(zaptest.NewLogger(t), tokenTypeSimple, dummyIndexWaiter, time.Second)
	require.NoError(t, err)
	as := NewAuthStore(zaptest.NewLogger(t), newBackendMock(), tp, bcrypt.MinCost)
	defer as.Close()
	require.NoError(t, enableAuthAndCreateRoot(as))
	_, err = as.UserAdd(&pb.AuthUserAddRequest{Name: "alice", Password: "pwd", Options: &authpb.UserAddOptions{}})
	require.NoError(t, err)

	ctx := context.WithValue(context.WithValue(t.Context(), AuthenticateParamIndex{}, uint64(10)), AuthenticateParamSimpleTokenPrefix{}, "pfx")
	resp, err := as.Authenticate(ctx, "alice", "pwd")
	require.NoError(t, err)

	time.Sleep(3 * time.Second) // TTL 1s, keeper resolution 1s
	_, err = as.AuthInfoFromCtx(tokenCtx(t, resp.Token))
	require.ErrorIs(t, err, ErrInvalidAuthToken, "the token has expired")

	renewed, err := as.RenewToken(t.Context(), resp.Token)
	require.NoError(t, err, "an expired simple token is renewed")
	require.Equal(t, resp.Token, renewed)
	ai, err := as.AuthInfoFromCtx(tokenCtx(t, resp.Token))
	require.NoError(t, err)
	require.Equal(t, "alice", ai.Username, "the expired token authenticates again")
}

// A JWT whose exp has passed is renewed (jwt.WithoutClaimsValidation): a JWT, once issued,
// can be renewed for as long as its user name exists.
func TestRenewTokenJWTIgnoresExpiry(t *testing.T) {
	as := newJWTStoreTTL(t, "1s")
	_, err := as.UserAdd(&pb.AuthUserAddRequest{Name: "alice", Password: "pwd", Options: &authpb.UserAddOptions{}})
	require.NoError(t, err)
	resp, err := as.Authenticate(t.Context(), "alice", "pwd")
	require.NoError(t, err)

	time.Sleep(2 * time.Second)
	_, err = as.AuthInfoFromCtx(tokenCtx(t, resp.Token))
	require.ErrorIs(t, err, ErrInvalidAuthToken, "the JWT has expired")

	renewed, err := as.RenewToken(t.Context(), resp.Token)
	require.NoError(t, err, "an expired JWT is renewed")
	ai, err := as.AuthInfoFromCtx(tokenCtx(t, renewed))
	require.NoError(t, err)
	require.Equal(t, "alice", ai.Username)
}

// A JWT issued before a password change is rejected by every permission check
// (ErrAuthOldRevision: the auth revision is etcd's revocation of JWTs, which carry no
// server-side state). RenewToken re-issues it at the current revision, and the new token
// passes the permission check.
func TestRenewTokenJWTSurvivesPasswordChange(t *testing.T) {
	as := newJWTStoreTTL(t, "5m")
	_, err := as.UserAdd(&pb.AuthUserAddRequest{Name: "alice", Password: "pwd", Options: &authpb.UserAddOptions{}})
	require.NoError(t, err)
	_, err = as.RoleAdd(&pb.AuthRoleAddRequest{Name: "rw"})
	require.NoError(t, err)
	_, err = as.RoleGrantPermission(&pb.AuthRoleGrantPermissionRequest{Name: "rw",
		Perm: &authpb.Permission{PermType: authpb.READWRITE, Key: []byte("foo"), RangeEnd: []byte("fop")}})
	require.NoError(t, err)
	_, err = as.UserGrantRole(&pb.AuthUserGrantRoleRequest{User: "alice", Role: "rw"})
	require.NoError(t, err)

	leaked, err := as.Authenticate(t.Context(), "alice", "pwd")
	require.NoError(t, err)
	ai, err := as.AuthInfoFromCtx(tokenCtx(t, leaked.Token))
	require.NoError(t, err)
	require.NoError(t, as.IsPutPermitted(ai, []byte("foo1")))

	// The administrator revokes the leaked credential by changing alice's password.
	_, err = as.UserChangePassword(&pb.AuthUserChangePasswordRequest{Name: "alice", HashedPassword: encodePassword("new")})
	require.NoError(t, err)
	ai, err = as.AuthInfoFromCtx(tokenCtx(t, leaked.Token))
	require.NoError(t, err)
	require.ErrorIs(t, as.IsPutPermitted(ai, []byte("foo1")), ErrAuthOldRevision, "the old token is revoked")

	renewed, err := as.RenewToken(t.Context(), leaked.Token)
	require.NoError(t, err, "the revoked token is renewed")
	ai, err = as.AuthInfoFromCtx(tokenCtx(t, renewed))
	require.NoError(t, err)
	require.NoError(t, as.IsPutPermitted(ai, []byte("foo1")), "the renewed token writes again")
}

// A JWT of a deleted user is renewed as soon as a user of the same name exists again.
func TestRenewTokenJWTDeletedUserRecreated(t *testing.T) {
	as := newJWTStoreTTL(t, "5m")
	_, err := as.UserAdd(&pb.AuthUserAddRequest{Name: "alice", Password: "pwd", Options: &authpb.UserAddOptions{}})
	require.NoError(t, err)
	old, err := as.Authenticate(t.Context(), "alice", "pwd")
	require.NoError(t, err)
	_, err = as.UserDelete(&pb.AuthUserDeleteRequest{Name: "alice"})
	require.NoError(t, err)
	_, err = as.RenewToken(t.Context(), old.Token)
	require.ErrorIs(t, err, ErrUserNotFound)

	_, err = as.UserAdd(&pb.AuthUserAddRequest{Name: "alice", Password: "other", Options: &authpb.UserAddOptions{}})
	require.NoError(t, err)
	renewed, err := as.RenewToken(t.Context(), old.Token)
	require.NoError(t, err, "the deleted user's token is renewed for the new user")
	ai, err := as.AuthInfoFromCtx(tokenCtx(t, renewed))
	require.NoError(t, err)
	require.Equal(t, as.Revision(), ai.Revision)
}

// slowUserBackend's read transactions report "victim" missing, after a delay: the window in
// which UserDelete's apply has deleted the user but not yet called invalidateUser.
type slowUserBackend struct{ *backendMock }

type slowUserTx struct{ AuthReadTx }

func (b slowUserBackend) ReadTx() AuthReadTx { return slowUserTx{b.backendMock.ReadTx()} }

func (tx slowUserTx) UnsafeGetUser(name string) *authpb.User {
	if name == "victim" {
		time.Sleep(200 * time.Millisecond)
		return nil
	}
	return tx.AuthReadTx.UnsafeGetUser(name)
}

// RenewToken runs on a request goroutine and calls tokenProvider.invalidateUser, which reads
// tokenSimple.simpleTokenKeeper without simpleTokensMu; tokenSimple.disable (AuthDisable, on
// the apply goroutine) writes it under the mutex. Run with -race: a data race is reported.
func TestRenewTokenInvalidateUserRacesDisable(t *testing.T) {
	be := slowUserBackend{newBackendMock()}
	tp, err := NewTokenProvider(zaptest.NewLogger(t), tokenTypeSimple, dummyIndexWaiter, simpleTokenTTLDefault)
	require.NoError(t, err)
	as := NewAuthStore(zaptest.NewLogger(t), be, tp, bcrypt.MinCost)
	defer as.Close()
	require.NoError(t, enableAuthAndCreateRoot(as))
	// "victim" exists for Authenticate (backendMock's BatchTx); the slow ReadTx hides it.
	_, err = as.UserAdd(&pb.AuthUserAddRequest{Name: "victim", Password: "pwd", Options: &authpb.UserAddOptions{}})
	require.NoError(t, err)
	ctx := context.WithValue(context.WithValue(t.Context(), AuthenticateParamIndex{}, uint64(10)), AuthenticateParamSimpleTokenPrefix{}, "pfx")
	resp, err := as.Authenticate(ctx, "victim", "pwd")
	require.NoError(t, err)

	done := make(chan struct{})
	go func() {
		defer close(done)
		time.Sleep(50 * time.Millisecond)
		as.AuthDisable() // the apply goroutine
	}()
	_, err = as.RenewToken(t.Context(), resp.Token)
	require.ErrorIs(t, err, ErrUserNotFound)
	<-done
}
