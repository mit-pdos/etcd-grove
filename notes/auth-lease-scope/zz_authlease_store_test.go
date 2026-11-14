// Evidence for notes/auth-lease-scope.md (auth-lease Scope, 2026-11-14), at the etcd pin 2eaeb872bc.
// Copy into server/auth and run: GOWORK=off go test ./auth/ -run TestAuthLeaseScope -v
package auth

import (
	"context"
	"strings"
	"testing"

	"github.com/stretchr/testify/require"
	"google.golang.org/grpc/metadata"

	"go.etcd.io/etcd/api/v3/v3rpc/rpctypes"
)

// §4 E5: IsAdminPermitted does not look at the auth info's revision, isOpPermitted does. So at
// apply, checkLeasePutsKeys' admin shortcut lets a root header with a stale revision revoke a
// lease with keys, where IsPutPermitted of the same header would refuse (ErrAuthOldRevision).
func TestAuthLeaseScopeAdminIgnoresRevision(t *testing.T) {
	as, tearDown := setupAuthStore(t)
	defer tearDown(t)

	cur := as.Revision()
	require.Greater(t, cur, uint64(1))
	stale := &AuthInfo{Username: "root", Revision: 1}
	require.NoError(t, as.IsAdminPermitted(stale), "admin check ignores the revision")
	require.ErrorIs(t, as.IsPutPermitted(stale, []byte("k")), ErrAuthOldRevision)

	// The empty user: refused by both (the apply thread's header of a token-less request).
	require.ErrorIs(t, as.IsAdminPermitted(&AuthInfo{}), ErrUserEmpty)
	require.ErrorIs(t, as.IsPutPermitted(&AuthInfo{}, []byte("k")), ErrUserEmpty)
}

// §4 E7: WithRoot (the expiry path's context, server.go revokeExpiredLeases) mints a simple
// token "<16 letters>.0" off the apply thread, assigned in the provider's map to root; the
// provider panics if the same token is assigned twice (assignSimpleTokenToUser).
func TestAuthLeaseScopeWithRootToken(t *testing.T) {
	as, tearDown := setupAuthStore(t)
	defer tearDown(t)

	ctx := as.WithRoot(context.Background())
	md, ok := metadata.FromIncomingContext(ctx)
	require.True(t, ok)
	tok := md[rpctypes.TokenFieldNameGRPC][0]
	parts := strings.Split(tok, ".")
	require.Len(t, parts, 2)
	require.Len(t, parts[0], defaultSimpleTokenLength)
	require.Equal(t, "0", parts[1], "the root token's index is 0")
	ai, err := as.AuthInfoFromCtx(ctx)
	require.NoError(t, err)
	require.Equal(t, "root", ai.Username)

	// A second WithRoot draws a fresh random prefix.
	tok2 := func() string {
		md2, _ := metadata.FromIncomingContext(as.WithRoot(context.Background()))
		return md2[rpctypes.TokenFieldNameGRPC][0]
	}()
	require.NotEqual(t, tok, tok2)

	// Assigning an already-assigned token panics: only the prefix's randomness keeps two
	// WithRoot calls apart.
	ts := as.tokenProvider.(*tokenSimple)
	actx := context.WithValue(context.WithValue(context.Background(), AuthenticateParamIndex{}, uint64(0)),
		AuthenticateParamSimpleTokenPrefix{}, parts[0])
	require.Panics(t, func() { _, _ = ts.assign(actx, "root", 0) })
}
