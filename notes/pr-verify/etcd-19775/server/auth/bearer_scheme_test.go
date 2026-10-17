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
	"errors"
	"testing"

	"google.golang.org/grpc/metadata"

	"go.etcd.io/etcd/api/v3/v3rpc/rpctypes"
)

// TestBearerSchemeForms records which forms of a bearer-prefixed token AuthInfoFromCtx accepts,
// under both metadata keys ("token" from gRPC clients, "authorization" from the gateway). It
// passes unchanged with strings.TrimPrefix(ts[0], "Bearer ") (etcd-io/etcd#21910, on main) and
// with the HasPrefix/slice of etcd-io/etcd#19775: the two are the same function.
func TestBearerSchemeForms(t *testing.T) {
	as, tearDown := setupAuthStore(t)
	defer tearDown(t)

	ctx := context.WithValue(context.WithValue(t.Context(), AuthenticateParamIndex{}, uint64(1)), AuthenticateParamSimpleTokenPrefix{}, "dummy")
	resp, err := as.Authenticate(ctx, "foo", "bar")
	if err != nil {
		t.Fatal(err)
	}
	tok := resp.Token

	cases := []struct {
		name  string
		value string
		ok    bool
	}{
		{"bare", tok, true},
		{"Bearer", "Bearer " + tok, true},
		{"Bearer twice", "Bearer Bearer " + tok, false}, // only one prefix is stripped
		{"lower-case scheme", "bearer " + tok, false},  // the scheme is matched case-sensitively
		{"upper-case scheme", "BEARER " + tok, false},
		{"two spaces", "Bearer  " + tok, false},
		{"tab", "Bearer\t" + tok, false},
		{"prefix only", "Bearer ", false},
	}
	for _, key := range []string{rpctypes.TokenFieldNameGRPC, rpctypes.TokenFieldNameSwagger} {
		for _, c := range cases {
			ctx := metadata.NewIncomingContext(t.Context(), metadata.New(map[string]string{key: c.value}))
			ai, err := as.AuthInfoFromCtx(ctx)
			if c.ok {
				if err != nil || ai == nil || ai.Username != "foo" {
					t.Errorf("%s/%s: want foo, got (%v, %v)", key, c.name, ai, err)
				}
			} else if !errors.Is(err, ErrInvalidAuthToken) {
				t.Errorf("%s/%s: want ErrInvalidAuthToken, got (%v, %v)", key, c.name, ai, err)
			}
		}
	}
}
