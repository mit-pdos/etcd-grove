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

package grpcproxy

import (
	"context"
	"net"
	"testing"

	"google.golang.org/grpc"
	"google.golang.org/grpc/codes"
	"google.golang.org/grpc/credentials/insecure"
	"google.golang.org/grpc/status"
	"google.golang.org/grpc/test/bufconn"

	pb "go.etcd.io/etcd/api/v3/etcdserverpb"
	"go.etcd.io/etcd/api/v3/v3rpc/rpctypes"
	clientv3 "go.etcd.io/etcd/client/v3"
	"go.etcd.io/etcd/server/v3/proxy/grpcproxy/cache"
)

// errKV is a clientv3.KV whose Do returns what the real client's kv.Do
// returns when the server answers ErrGRPCNoLeader: ContextError(ctx,
// ErrGRPCNoLeader) = rpctypes.ErrNoLeader, an EtcdError.
type errKV struct {
	clientv3.KV
	err error
}

func (k errKV) Do(context.Context, clientv3.Op) (clientv3.OpResponse, error) {
	return clientv3.OpResponse{}, k.err
}

// The proxy returns the client's EtcdError as is; EtcdError has no
// GRPCStatus method, so grpc sends it with code Unknown, losing the server's
// code (Unavailable for ErrNoLeader, InvalidArgument for ErrEmptyKey).
func TestProxyKVErrorCode(t *testing.T) {
	for _, tc := range []struct {
		err  error
		want codes.Code
	}{
		{rpctypes.ErrNoLeader, codes.Unavailable},
		{rpctypes.ErrEmptyKey, codes.InvalidArgument},
	} {
		lis := bufconn.Listen(1 << 20)
		srv := grpc.NewServer()
		pb.RegisterKVServer(srv, &kvProxy{kv: errKV{err: tc.err}, cache: cache.NewCache(1)})
		go srv.Serve(lis)
		conn, err := grpc.NewClient("passthrough:///bufnet",
			grpc.WithContextDialer(func(context.Context, string) (net.Conn, error) { return lis.Dial() }),
			grpc.WithTransportCredentials(insecure.NewCredentials()))
		if err != nil {
			t.Fatal(err)
		}
		_, err = pb.NewKVClient(conn).Range(context.Background(), &pb.RangeRequest{Key: []byte("a")})
		if got := status.Code(err); got != tc.want {
			t.Errorf("proxy Range with backend error %v: code %v, want %v (as from the server directly)", tc.err, got, tc.want)
		}
		conn.Close()
		srv.Stop()
	}
}
