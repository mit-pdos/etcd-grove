package v3rpc

import (
	"context"
	"testing"

	"google.golang.org/grpc"
	"google.golang.org/grpc/peer"
)

// A Peer without an Addr in a unary request's context: the PR's log interceptor calls
// peerInfo.Addr.String() before the handler, on every request (before the PR, only when
// request stats were logged).
func TestReviewLogInterceptorNilPeerAddr(t *testing.T) {
	ic := newLogUnaryInterceptor(nil)
	ctx := peer.NewContext(context.Background(), &peer.Peer{})
	defer func() {
		r := recover()
		t.Logf("recovered: %v", r)
		if r == nil {
			t.Fatal("expected a panic")
		}
	}()
	ic(ctx, nil, &grpc.UnaryServerInfo{FullMethod: "/x"}, func(ctx context.Context, req any) (any, error) {
		t.Fatal("handler reached")
		return nil, nil
	})
}
