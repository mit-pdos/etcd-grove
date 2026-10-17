package auth

import (
	"context"
	"testing"

	"github.com/prometheus/client_golang/prometheus/testutil"
)

// TestReviewWithRootCountsTokens: WithRoot (called by /health handlers and by lease-revoke
// goroutines, not the apply goroutine) assigns a fresh simple token each call; the gauge counts
// them, and with the default TTL each lives 300s (with --auth-token-ttl of years, forever).
func TestReviewWithRootCountsTokens(t *testing.T) {
	as, tearDown := setupAuthStore(t)
	defer tearDown(t)
	base := int(testutil.ToFloat64(simpleTokenGauge))
	for i := 0; i < 50; i++ {
		as.WithRoot(context.Background())
	}
	got := int(testutil.ToFloat64(simpleTokenGauge))
	t.Logf("gauge before %d, after 50 WithRoot calls %d", base, got)
	if got != base+50 {
		t.Errorf("expected %d, got %d", base+50, got)
	}
}

// TestReviewRecoverDisabledKeepsTokens: Recover from a backend where auth is disabled sets
// as.enabled = false but does not disable the token provider (pre-existing): the tokens and the
// gauge stay, and a later AuthEnable (enable() is a no-op: the keeper is non-nil) revalidates the
// old tokens.
func TestReviewRecoverDisabledKeepsTokens(t *testing.T) {
	as, tearDown := setupAuthStore(t)
	defer tearDown(t)
	ts := as.tokenProvider.(*tokenSimple)
	ctx := context.WithValue(context.WithValue(context.Background(), AuthenticateParamIndex{}, uint64(1)),
		AuthenticateParamSimpleTokenPrefix{}, "oldprefix")
	tok, err := as.Authenticate(ctx, "foo", "bar")
	if err != nil {
		t.Fatal(err)
	}
	be := as.be.(*backendMock)
	be.enabled = false
	as.Recover(be)
	ts.simpleTokensMu.Lock()
	n := len(ts.simpleTokens)
	ts.simpleTokensMu.Unlock()
	t.Logf("after Recover(auth disabled): IsAuthEnabled=%v, tokens %d, gauge %v",
		as.IsAuthEnabled(), n, testutil.ToFloat64(simpleTokenGauge))
	if err := as.AuthEnable(); err != nil {
		t.Fatal(err)
	}
	_, ok := ts.info(context.Background(), tok.Token, 0)
	t.Logf("after AuthEnable: token issued before the disable still valid: %v", ok)
}
