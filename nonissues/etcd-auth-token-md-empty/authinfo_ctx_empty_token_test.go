package auth

import (
	"context"
	"testing"

	"go.uber.org/zap/zaptest"
	"google.golang.org/grpc/metadata"
)

// TestAuthInfoFromCtxEmptyTokenValues: AuthInfoFromCtx on incoming metadata
// with a "token" key and no value should return no token (or an error); it
// indexes ts[0] and panics. gRPC's transports never build such metadata; only
// an in-process caller can. Uses dummyIndexWaiter from the package's tests.
func TestAuthInfoFromCtxEmptyTokenValues(t *testing.T) {
	tp, err := NewTokenProvider(zaptest.NewLogger(t), tokenTypeSimple, dummyIndexWaiter, simpleTokenTTLDefault)
	if err != nil {
		t.Fatal(err)
	}
	as := &authStore{lg: zaptest.NewLogger(t), enabled: true, tokenProvider: tp}
	ctx := metadata.NewIncomingContext(context.Background(), metadata.MD{"token": {}})
	defer func() {
		if r := recover(); r != nil {
			t.Fatalf("AuthInfoFromCtx panicked on an empty token list: %v", r)
		}
	}()
	as.AuthInfoFromCtx(ctx)
}
