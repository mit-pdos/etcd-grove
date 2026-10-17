package auth

import (
	"context"
	"testing"
	"time"

	"github.com/stretchr/testify/require"
	"go.uber.org/zap/zaptest"
	"golang.org/x/crypto/bcrypt"
	"google.golang.org/grpc/metadata"

	"go.etcd.io/etcd/api/v3/v3rpc/rpctypes"
)

// A TTL-expired simple token is rejected by AuthInfoFromCtx (every API). One RenewToken
// call (which v3client makes on behalf of any v3lock/v3election request carrying it) puts the
// token back in the live table: from then on the client's own expired token works again on
// every API of this member, not only inside the in-process client.
func TestReviewerRenewRevivesExpiredSimpleTokenForAllAPIs(t *testing.T) {
	oldRes := simpleTokenTTLResolution
	simpleTokenTTLResolution = 10 * time.Millisecond
	defer func() { simpleTokenTTLResolution = oldRes }()

	tp, err := NewTokenProvider(zaptest.NewLogger(t), tokenTypeSimple, dummyIndexWaiter, 100*time.Millisecond)
	require.NoError(t, err)
	as := NewAuthStore(zaptest.NewLogger(t), newBackendMock(), tp, bcrypt.MinCost)
	defer as.Close()
	require.NoError(t, enableAuthAndCreateRoot(as))

	ctx := context.WithValue(context.WithValue(t.Context(), AuthenticateParamIndex{}, uint64(1)), AuthenticateParamSimpleTokenPrefix{}, "pfx")
	resp, err := as.Authenticate(ctx, "root", "root")
	require.NoError(t, err)
	md := metadata.NewIncomingContext(t.Context(), metadata.Pairs(rpctypes.TokenFieldNameGRPC, resp.Token))

	time.Sleep(500 * time.Millisecond)
	_, err = as.AuthInfoFromCtx(md)
	require.ErrorIs(t, err, ErrInvalidAuthToken, "token should have expired")

	_, err = as.RenewToken(t.Context(), resp.Token)
	require.NoError(t, err)

	ai, err := as.AuthInfoFromCtx(md)
	require.NoError(t, err)
	t.Logf("expired token accepted again for user %q on every API", ai.Username)
}
