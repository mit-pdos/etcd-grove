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

import (
	"context"
	"testing"
	"time"

	"go.uber.org/zap"
	"go.uber.org/zap/zapcore"
	"go.uber.org/zap/zaptest/observer"
	"google.golang.org/grpc"
	"google.golang.org/grpc/codes"
	"google.golang.org/grpc/credentials/insecure"
	"google.golang.org/grpc/status"

	pb "go.etcd.io/etcd/api/v3/etcdserverpb"
)

// canceledAuthRemote answers Authenticate as a grpc connection does once the
// caller's context is canceled: a Canceled status.
type canceledAuthRemote struct {
	pb.AuthClient
}

func (canceledAuthRemote) Authenticate(ctx context.Context, in *pb.AuthenticateRequest, opts ...grpc.CallOption) (*pb.AuthenticateResponse, error) {
	return nil, status.Error(codes.Canceled, "context canceled")
}

func newShutdownTestClient(t *testing.T) (*Client, *observer.ObservedLogs) {
	core, logs := observer.New(zapcore.DebugLevel)
	c := &Client{Username: "user", Password: "pass"}
	c.lg.Store(zap.New(core))
	c.Auth = NewAuthFromAuthClient(canceledAuthRemote{}, c)
	return c, logs
}

func warnOrAbove(logs *observer.ObservedLogs) []observer.LoggedEntry {
	var out []observer.LoggedEntry
	for _, e := range logs.All() {
		if e.Level >= zapcore.WarnLevel {
			out = append(out, e)
		}
	}
	return out
}

// TestStreamInterceptorGetTokenCanceledLogs: the stream interceptor's getToken
// under a canceled context. Authenticate's ContextError turns the Canceled
// status into ctx.Err(), the bare context.Canceled, for which isContextError
// is false (status.Code(context.Canceled) is Unknown): "getToken failed" is
// still logged at Error, the log line of etcd-io/etcd#21643.
func TestStreamInterceptorGetTokenCanceledLogs(t *testing.T) {
	c, logs := newShutdownTestClient(t)
	ctx, cancel := context.WithCancel(context.Background())
	cancel()

	err := c.getToken(ctx)
	t.Logf("getToken: %v (%T), isContextError=%v, status.Code=%v", err, err, isContextError(err), status.Code(err))

	si := c.streamClientInterceptor(withMax(5))
	streamer := func(ctx context.Context, desc *grpc.StreamDesc, cc *grpc.ClientConn, method string, opts ...grpc.CallOption) (grpc.ClientStream, error) {
		t.Fatal("streamer called after getToken failed")
		return nil, nil
	}
	_, err = si(ctx, &grpc.StreamDesc{ServerStreams: true}, nil, "/etcdserverpb.Watch/Watch", streamer)
	if err == nil {
		t.Fatal("expected an error")
	}
	for _, e := range warnOrAbove(logs) {
		t.Logf("logged %v %q", e.Level, e.Message)
	}
	if n := len(warnOrAbove(logs)); n != 0 {
		t.Errorf("expected no warn/error log on a canceled context, got %d", n)
	}
}

// TestStreamInterceptorStreamerCanceledQuiet: the streamer failing with a
// Canceled status under a canceled context is not logged.
func TestStreamInterceptorStreamerCanceledQuiet(t *testing.T) {
	c, logs := newShutdownTestClient(t)
	c.Username, c.Password = "", "" // getToken returns nil
	ctx, cancel := context.WithCancel(context.Background())
	cancel()
	si := c.streamClientInterceptor(withMax(5))
	streamer := func(ctx context.Context, desc *grpc.StreamDesc, cc *grpc.ClientConn, method string, opts ...grpc.CallOption) (grpc.ClientStream, error) {
		return nil, status.Error(codes.Canceled, "context canceled")
	}
	if _, err := si(ctx, &grpc.StreamDesc{ServerStreams: true}, nil, "/etcdserverpb.Watch/Watch", streamer); err == nil {
		t.Fatal("expected an error")
	}
	if n := len(warnOrAbove(logs)); n != 0 {
		t.Errorf("expected no warn/error log, got %d: %v", n, warnOrAbove(logs))
	}
}

// TestUnaryInterceptorCanceledQuiet: the unary interceptor, an invoker failing
// with a Canceled status under a canceled context: no warning, one attempt.
func TestUnaryInterceptorCanceledQuiet(t *testing.T) {
	c, logs := newShutdownTestClient(t)
	cc, err := grpc.NewClient("passthrough:///unused", grpc.WithTransportCredentials(insecure.NewCredentials()))
	if err != nil {
		t.Fatal(err)
	}
	defer cc.Close()
	ctx, cancel := context.WithCancel(context.Background())
	cancel()
	ui := c.unaryClientInterceptor(withMax(5), withBackoff(func(uint) time.Duration { return 0 }))
	calls := 0
	invoker := func(ctx context.Context, method string, req, reply any, cc *grpc.ClientConn, opts ...grpc.CallOption) error {
		calls++
		return status.Error(codes.Canceled, "context canceled")
	}
	err = ui(ctx, "/etcdserverpb.Auth/Authenticate", nil, nil, cc, invoker)
	if status.Code(err) != codes.Canceled || calls != 1 {
		t.Fatalf("err %v, calls %d", err, calls)
	}
	if n := len(warnOrAbove(logs)); n != 0 {
		t.Errorf("expected no warn/error log, got %d: %v", n, warnOrAbove(logs))
	}
}

// TestUnaryInterceptorLiveCtxCanceledStatusSilent: with the caller's context
// live, a Canceled (or DeadlineExceeded) status (from the server, or a proxy) is
// retried up to max times, each attempt now silently: before the change each
// failed attempt logged "retrying of unary invoker failed".
func TestUnaryInterceptorLiveCtxCanceledStatusSilent(t *testing.T) {
	c, logs := newShutdownTestClient(t)
	cc, err := grpc.NewClient("passthrough:///unused", grpc.WithTransportCredentials(insecure.NewCredentials()))
	if err != nil {
		t.Fatal(err)
	}
	defer cc.Close()
	ui := c.unaryClientInterceptor(withMax(5), withBackoff(func(uint) time.Duration { return 0 }))
	calls := 0
	invoker := func(ctx context.Context, method string, req, reply any, cc *grpc.ClientConn, opts ...grpc.CallOption) error {
		calls++
		return status.Error(codes.DeadlineExceeded, "server-side deadline")
	}
	err = ui(context.Background(), "/etcdserverpb.KV/Put", nil, nil, cc, invoker)
	t.Logf("err %v, calls %d, warn+ logs %d", err, calls, len(warnOrAbove(logs)))
	if n := len(warnOrAbove(logs)); n != 0 {
		t.Errorf("warn/error logs: %d", n)
	}
}
