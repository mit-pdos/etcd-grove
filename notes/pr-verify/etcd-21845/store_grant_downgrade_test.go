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
	"testing"

	"github.com/stretchr/testify/require"

	"go.etcd.io/etcd/api/v3/authpb"
	pb "go.etcd.io/etcd/api/v3/etcdserverpb"
)

// TestRoleGrantPermissionDowngradeSameKey: a role holds write on [foo, fop)
// and on [foo, foq); granting read on [foo, foq) is meant to downgrade the
// second permission. Before the fix, RoleGrantPermission finds only the first
// permission with Key "foo" ([foo, fop)), appends a read [foo, foq) beside the
// write one, and the user can still write "fop".
func TestRoleGrantPermissionDowngradeSameKey(t *testing.T) {
	as, tearDown := setupAuthStore(t)
	defer tearDown(t)

	_, err := as.RoleAdd(&pb.AuthRoleAddRequest{Name: "role-test-1"})
	require.NoError(t, err)
	grant := func(rangeEnd string, pt authpb.Permission_Type) {
		t.Helper()
		_, err := as.RoleGrantPermission(&pb.AuthRoleGrantPermissionRequest{
			Name: "role-test-1",
			Perm: &authpb.Permission{PermType: pt, Key: []byte("foo"), RangeEnd: []byte(rangeEnd)},
		})
		require.NoError(t, err)
	}
	grant("fop", authpb.Permission_WRITE)
	grant("foq", authpb.Permission_WRITE)
	_, err = as.UserGrantRole(&pb.AuthUserGrantRoleRequest{User: "foo", Role: "role-test-1"})
	require.NoError(t, err)
	require.NoError(t, as.isOpPermitted("foo", as.Revision(), []byte("fop"), nil, authpb.Permission_WRITE))

	// downgrade [foo, foq) to read
	grant("foq", authpb.Permission_READ)

	require.ErrorIs(t, as.isOpPermitted("foo", as.Revision(), []byte("fop"), nil, authpb.Permission_WRITE), ErrPermissionDenied,
		"write on fop still permitted after downgrading [foo, foq) to read")
	require.NoError(t, as.isOpPermitted("foo", as.Revision(), []byte("fop"), nil, authpb.Permission_READ))

	r, err := as.RoleGet(&pb.AuthRoleGetRequest{Role: "role-test-1"})
	require.NoError(t, err)
	require.Lenf(t, r.Perm, 2, "permissions after the downgrade: %v", r.Perm)
}
