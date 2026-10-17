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

package auth

import (
	"fmt"
	"testing"

	"github.com/stretchr/testify/require"
	"go.uber.org/zap/zaptest"
	"golang.org/x/crypto/bcrypt"
)

// TestWithRootVerifyOnlyJWTIsUnauthenticated shows that on a member whose JWT
// provider has only a public key (verify-only), WithRoot cannot sign a root
// token and returns the context unchanged, so the server's internal requests
// built on it (revokeExpiredLeases's LeaseRevoke, the /health and /readyz
// range checks) run with no user and are refused with ErrUserEmpty.
func TestWithRootVerifyOnlyJWTIsUnauthenticated(t *testing.T) {
	opts := fmt.Sprintf("%s,pub-key=%s,sign-method=RS256", tokenTypeJWT, jwtRSAPubKey)
	tp, err := NewTokenProvider(zaptest.NewLogger(t), opts, dummyIndexWaiter, simpleTokenTTLDefault)
	require.NoError(t, err)
	as := NewAuthStore(zaptest.NewLogger(t), newBackendMock(), tp, bcrypt.MinCost)
	defer as.Close()
	require.NoError(t, enableAuthAndCreateRoot(as))

	ctx := t.Context()
	rootCtx := as.WithRoot(ctx)
	require.Same(t, ctx, rootCtx, "WithRoot could not sign a token and returned ctx unchanged")
	ai, err := as.AuthInfoFromCtx(rootCtx)
	require.NoError(t, err)
	require.Nil(t, ai, "no auth info: the internal request has no user")
	// The server then sends the request with an empty user name in its
	// header (processInternalRaftRequestOnce), which the apply side refuses.
	header := &AuthInfo{}
	require.ErrorIs(t, as.IsRangePermitted(header, []byte("key"), nil), ErrUserEmpty)
	require.ErrorIs(t, as.IsDeleteRangePermitted(header, []byte("key"), nil), ErrUserEmpty)
}
