package ctxvalue

import (
	"context"
	"fmt"
	"testing"

	"google.golang.org/grpc"
	"google.golang.org/protobuf/types/known/emptypb"
)

// Premise fixes 8, S2: authStore.AuthInfoFromTLS's spec takes peer.peerCtxOk and
// metadata.incomingCtxOk, authStore.AuthInfoFromCtx's metadata.incomingCtxOk (both from
// context.libCtxOk, which a grpc run context carries). On a TLS grpc server's handler context
// (ClientCertAuthEnabled's path), both run without a panic: AuthInfoFromTLS returns the client
// certificate's common name, AuthInfoFromCtx (auth disabled) nil and nil.
func TestAuthInfoFromTLSReal(t *testing.T) {
	as := newAuthStore(t)
	got := make(chan string, 1)
	unary := func(srv any, ctx context.Context, dec func(any) error, _ grpc.UnaryServerInterceptor) (any, error) {
		in := new(emptypb.Empty)
		if err := dec(in); err != nil {
			return nil, err
		}
		res := ""
		func() {
			defer func() {
				if r := recover(); r != nil {
					res = fmt.Sprintf("panic: %v", r)
				}
			}()
			ai := as.AuthInfoFromTLS(ctx)
			if ai == nil {
				res = "AuthInfoFromTLS: nil"
				return
			}
			if ai.Username != "root" {
				res = "AuthInfoFromTLS: user " + ai.Username
				return
			}
			ai2, err := as.AuthInfoFromCtx(ctx)
			if ai2 != nil || err != nil {
				res = fmt.Sprintf("AuthInfoFromCtx: %v, %v", ai2, err)
			}
		}()
		got <- res
		return in, nil
	}
	cc := startServer(t, true, nil, unary, func(any, grpc.ServerStream) error { return nil })
	if err := cc.Invoke(context.Background(), "/t.S/U", new(emptypb.Empty), new(emptypb.Empty)); err != nil {
		t.Fatal(err)
	}
	if s := <-got; s != "" {
		t.Error(s)
	}
}
