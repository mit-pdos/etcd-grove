package auth

import (
	"testing"

	"github.com/stretchr/testify/require"
	"go.uber.org/zap/zaptest"
	"golang.org/x/crypto/bcrypt"
	"google.golang.org/grpc/metadata"

	"go.etcd.io/etcd/api/v3/authpb"
	pb "go.etcd.io/etcd/api/v3/etcdserverpb"
	"go.etcd.io/etcd/api/v3/v3rpc/rpctypes"
)

// A user token installed (as incoming metadata) on a context derived from a root context:
// with WithRoot the later token wins (the request runs as the user); with WithRootInternal's
// JWT fast path the root value wins over any later token.
func TestWithRootInternalNotDowngradedByLaterToken(t *testing.T) {
	tp, err := NewTokenProvider(zaptest.NewLogger(t), testJWTOpts(), dummyIndexWaiter, simpleTokenTTLDefault)
	require.NoError(t, err)
	as := NewAuthStore(zaptest.NewLogger(t), newBackendMock(), tp, bcrypt.MinCost).(*authStore)
	defer as.Close()
	_, err = as.UserAdd(&pb.AuthUserAddRequest{Name: "limited", HashedPassword: encodePassword("x"), Options: &authpb.UserAddOptions{}})
	require.NoError(t, err)
	require.NoError(t, enableAuthAndCreateRoot(as))
	userTok, err := tp.assign(t.Context(), "limited", as.Revision())
	require.NoError(t, err)

	oldCtx := metadata.NewIncomingContext(as.WithRoot(t.Context()), metadata.Pairs(rpctypes.TokenFieldNameGRPC, userTok))
	ai, err := as.AuthInfoFromCtx(oldCtx)
	require.NoError(t, err)
	require.Equal(t, "limited", ai.Username)

	newCtx := metadata.NewIncomingContext(WithRootInternal(t.Context(), as), metadata.Pairs(rpctypes.TokenFieldNameGRPC, userTok))
	ai, err = as.AuthInfoFromCtx(newCtx)
	require.NoError(t, err)
	require.Equal(t, "root", ai.Username) // differs from WithRoot
}
