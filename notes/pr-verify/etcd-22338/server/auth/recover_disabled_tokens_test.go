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
	"context"
	"testing"
)

// TestRecoverAuthDisabledKeepsSimpleTokens: Recover from a backend in which auth is disabled (a
// member that applies a snapshot taken after AuthDisable) sets as.enabled = false but does not
// disable the token provider, so the simple tokens issued before stay in memory, and after a
// later AuthEnable (whose enable() does nothing: the keeper is still there) they are accepted
// again on this member, while AuthDisable dropped them on the members that applied it.
func TestRecoverAuthDisabledKeepsSimpleTokens(t *testing.T) {
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
	be.enabled = false // the snapshot's backend: auth disabled
	as.Recover(be)
	if as.IsAuthEnabled() {
		t.Fatal("auth still enabled after Recover")
	}
	ts.simpleTokensMu.Lock()
	n := len(ts.simpleTokens)
	ts.simpleTokensMu.Unlock()
	t.Logf("after Recover (auth disabled): %d simple token(s) still in memory", n)

	if err := as.AuthEnable(); err != nil {
		t.Fatal(err)
	}
	if _, ok := ts.info(context.Background(), tok.Token, 0); ok {
		t.Errorf("token %q issued before auth was disabled is valid again after re-enabling", tok.Token)
	}
}
