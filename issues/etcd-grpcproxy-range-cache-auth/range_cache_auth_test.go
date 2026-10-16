// Reproduction for issues/etcd-grpcproxy-range-cache-auth.md (etcd-io/etcd#22065).
//
// Drop into go.etcd.io/etcd/server/v3/proxy/grpcproxy (repository etcd-io/etcd, or the fork
// upamanyus/etcd at the pinned revision 107edf7e492a5cd7e8d958ed8a7ac9dbf1ecf81f), then run, from
// the module directory server/:
//
//	go test ./proxy/grpcproxy/ -run TestRangeCacheIgnoresCaller -v
//
// Passes at the pin: a serializable Range from a caller without a token is answered from the
// cache entry a token-carrying caller's Range filled, and the backend (which would deny it) is
// not asked. The check states the buggy behavior.
package grpcproxy

import (
	"context"
	"testing"

	"google.golang.org/grpc/metadata"

	pb "go.etcd.io/etcd/api/v3/etcdserverpb"
	"go.etcd.io/etcd/api/v3/mvccpb"
	"go.etcd.io/etcd/api/v3/v3rpc/rpctypes"
	clientv3 "go.etcd.io/etcd/client/v3"
	"go.etcd.io/etcd/server/v3/proxy/grpcproxy/cache"
)

// authKV stands for an auth-enabled backend: it serves a Range only to a context carrying a
// token, and counts the requests it sees.
type authKV struct {
	clientv3.KV
	calls int
}

func (a *authKV) Do(ctx context.Context, op clientv3.Op) (clientv3.OpResponse, error) {
	a.calls++
	md, _ := metadata.FromIncomingContext(ctx)
	if len(md[rpctypes.TokenFieldNameGRPC]) == 0 {
		return clientv3.OpResponse{}, rpctypes.ErrGRPCUserEmpty
	}
	resp := &clientv3.GetResponse{
		Header: &pb.ResponseHeader{Revision: 2},
		Kvs:    []*mvccpb.KeyValue{{Key: []byte("/secret"), Value: []byte("v"), ModRevision: 2}},
		Count:  1,
	}
	return resp.OpResponse(), nil
}

func TestRangeCacheIgnoresCaller(t *testing.T) {
	kv := &authKV{}
	p := &kvProxy{kv: kv, cache: cache.NewCache(cache.DefaultMaxEntries)}
	req := &pb.RangeRequest{Key: []byte("/secret"), Serializable: true}

	authed := metadata.NewIncomingContext(context.Background(),
		metadata.Pairs(rpctypes.TokenFieldNameGRPC, "token-of-an-authorized-user"))
	if _, err := p.Range(authed, req); err != nil {
		t.Fatalf("authorized Range: %v", err)
	}

	// The backend denies this caller (as the server does: "user name is empty").
	if _, err := kv.Do(context.Background(), clientv3.OpGet("/secret")); err == nil {
		t.Fatal("expected the backend to deny a caller without a token")
	}
	kv.calls = 0

	resp, err := p.Range(context.Background(), req)
	if err != nil {
		t.Fatalf("expected the cached response, got %v", err)
	}
	if kv.calls != 0 || len(resp.Kvs) != 1 || string(resp.Kvs[0].Value) != "v" {
		t.Fatalf("expected a cache hit with the value, got %v (backend calls %d)", resp, kv.calls)
	}
	t.Logf("caller without a token got %q from the cache; backend not consulted", resp.Kvs[0].Value)
}
