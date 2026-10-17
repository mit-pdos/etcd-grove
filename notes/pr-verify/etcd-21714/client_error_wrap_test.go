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

package clientv3

// Probes for etcd-io/etcd#21714 (wrap New's dial and token errors with the endpoints). Each test
// logs what a caller of New sees of the error (its message, `errors.Is`, `==`, a type assertion,
// grpc's status code) so that the same file, run at the PR's base and at its head, shows what
// changes. The assertions are the ones that hold at both revisions; the `PR21714_HEAD`
// environment variable selects the assertions that differ.

import (
	"context"
	"errors"
	"net"
	"os"
	"strings"
	"testing"
	"time"

	"github.com/stretchr/testify/require"
	"google.golang.org/grpc"
	"google.golang.org/grpc/status"

	"go.etcd.io/etcd/api/v3/etcdserverpb"
	"go.etcd.io/etcd/api/v3/v3rpc/rpctypes"
	"go.etcd.io/etcd/client/pkg/v3/testutil"
)

var atHead = os.Getenv("PR21714_HEAD") == "1"

type authFailedServer struct {
	etcdserverpb.UnimplementedAuthServer
}

func (authFailedServer) Authenticate(context.Context, *etcdserverpb.AuthenticateRequest) (*etcdserverpb.AuthenticateResponse, error) {
	return nil, rpctypes.ErrGRPCAuthFailed
}

func logErr(t *testing.T, err error) {
	var ee rpctypes.EtcdError
	_, isEtcd := err.(rpctypes.EtcdError)
	t.Logf("err.Error()                        = %q", err.Error())
	t.Logf("errors.Is(err, ErrAuthFailed)      = %v", errors.Is(err, rpctypes.ErrAuthFailed))
	t.Logf("err == ErrAuthFailed               = %v", err == error(rpctypes.ErrAuthFailed))
	t.Logf("errors.As(err, &EtcdError)         = %v", errors.As(err, &ee))
	t.Logf("err.(rpctypes.EtcdError) ok        = %v", isEtcd)
	t.Logf("errors.Is(err, DeadlineExceeded)   = %v", errors.Is(err, context.DeadlineExceeded))
	t.Logf("err == context.DeadlineExceeded    = %v", err == context.DeadlineExceeded)
	t.Logf("status.Code(err)                   = %v", status.Code(err))
	t.Logf("rpctypes.ErrorDesc(err)            = %q", rpctypes.ErrorDesc(err))
}

// A wrong password: the server's Authenticate fails, so New's getToken fails.
func TestPR21714TokenError(t *testing.T) {
	testutil.BeforeTest(t)
	lis, err := net.Listen("unix", "etcd-pr21714-auth:0")
	require.NoError(t, err)
	defer lis.Close()
	addr := "unix://" + lis.Addr().String()
	srv := grpc.NewServer()
	etcdserverpb.RegisterAuthServer(srv, authFailedServer{})
	go srv.Serve(lis)
	defer srv.Stop()

	c, err := New(Config{DialTimeout: 5 * time.Second, Endpoints: []string{addr}, Username: "u", Password: "wrong"})
	require.Nil(t, c)
	require.Error(t, err)
	logErr(t, err)
	// both revisions: errors.Is and errors.As find the typed error
	require.ErrorIs(t, err, rpctypes.ErrAuthFailed)
	var ee rpctypes.EtcdError
	require.ErrorAs(t, err, &ee)
	_, isEtcd := err.(rpctypes.EtcdError)
	if atHead {
		require.Contains(t, err.Error(), "etcdclient: communicating with ["+addr+"] failed: ")
		require.False(t, isEtcd, "the head wraps: a type assertion no longer finds rpctypes.EtcdError")
		require.NotEqual(t, error(rpctypes.ErrAuthFailed), err)
	} else {
		require.True(t, isEtcd)
		require.Equal(t, error(rpctypes.ErrAuthFailed), err)
	}
}

// An unreachable endpoint and no credentials: New does not fail at all (grpc.NewClient does not
// connect), at both revisions; the "dialing [...] failed" message does not appear for it.
func TestPR21714UnreachableNoAuth(t *testing.T) {
	lis, err := net.Listen("tcp", "127.0.0.1:0")
	require.NoError(t, err)
	addr := lis.Addr().String()
	lis.Close() // nothing listens there now
	c, err := New(Config{DialTimeout: time.Second, Endpoints: []string{addr}})
	require.NoError(t, err)
	defer c.Close()
	ctx, cancel := context.WithTimeout(context.Background(), time.Second)
	defer cancel()
	_, gerr := c.Get(ctx, "k")
	require.Error(t, gerr)
	t.Logf("New: no error; the first request fails instead: %q (no endpoint in it)", gerr.Error())
}

// An unreachable endpoint with a user name and password: getToken's request times out.
func TestPR21714UnreachableWithAuth(t *testing.T) {
	lis, err := net.Listen("tcp", "127.0.0.1:0")
	require.NoError(t, err)
	addr := lis.Addr().String()
	lis.Close()
	start := time.Now()
	c, err := New(Config{DialTimeout: time.Second, Endpoints: []string{addr}, Username: "u", Password: "p"})
	require.Nil(t, c)
	require.Error(t, err)
	t.Logf("after %v", time.Since(start).Round(100*time.Millisecond))
	logErr(t, err)
	require.ErrorIs(t, err, context.DeadlineExceeded)
	if atHead {
		require.Contains(t, err.Error(), "etcdclient: communicating with ["+addr+"] failed: ")
		require.NotEqual(t, context.DeadlineExceeded, err)
	} else {
		require.Equal(t, context.DeadlineExceeded, err)
	}
}

type secureOnlyCreds struct{}

func (secureOnlyCreds) GetRequestMetadata(context.Context, ...string) (map[string]string, error) {
	return nil, nil
}
func (secureOnlyCreds) RequireTransportSecurity() bool { return true }

// A dial that fails (grpc.NewClient's option check: per-RPC credentials that require transport
// security over an insecure connection): the head wraps the error with the endpoints.
func TestPR21714DialError(t *testing.T) {
	addr := "127.0.0.1:2379"
	c, err := New(Config{
		DialTimeout: time.Second,
		Endpoints:   []string{addr, "127.0.0.1:22379"},
		DialOptions: []grpc.DialOption{grpc.WithPerRPCCredentials(secureOnlyCreds{})},
	})
	require.Nil(t, c)
	require.Error(t, err)
	logErr(t, err)
	if atHead {
		require.True(t, strings.HasPrefix(err.Error(), "etcdclient: dialing [127.0.0.1:2379;127.0.0.1:22379] failed: "))
		require.NotNil(t, errors.Unwrap(err))
	} else {
		require.Nil(t, errors.Unwrap(err))
	}
}

// The mutually exclusive configuration: the same variable, a new message.
func TestPR21714MutuallyExclusive(t *testing.T) {
	_, err := New(Config{Endpoints: []string{"127.0.0.1:2379"}, Token: "t", Username: "u", Password: "p"})
	require.Equal(t, ErrMutuallyExclusiveCfg, err)
	t.Logf("err.Error() = %q", err.Error())
}
