package auth

import (
	"context"
	"testing"

	"go.uber.org/zap/zaptest"
	"google.golang.org/grpc/credentials/insecure"
	"google.golang.org/grpc/peer"
)

// TestAuthInfoFromTLSNonTLSPeer: AuthInfoFromTLS on a context whose peer has
// non-TLS auth info should return nil (no TLS identity), as for a peer without
// auth info; it panics on the type assertion.
func TestAuthInfoFromTLSNonTLSPeer(t *testing.T) {
	as := &authStore{lg: zaptest.NewLogger(t)}
	_, ai, _ := insecure.NewCredentials().ServerHandshake(nil)
	ctx := peer.NewContext(context.Background(), &peer.Peer{AuthInfo: ai})
	defer func() {
		if r := recover(); r != nil {
			t.Fatalf("AuthInfoFromTLS panicked on a non-TLS peer: %v", r)
		}
	}()
	if got := as.AuthInfoFromTLS(ctx); got != nil {
		t.Fatalf("AuthInfoFromTLS = %v, want nil", got)
	}
}
