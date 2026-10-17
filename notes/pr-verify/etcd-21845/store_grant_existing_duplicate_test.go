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

// TestRoleGrantPermissionExistingDuplicate: a role stored by an etcd without
// the fix can hold two permissions on one range. Before the fix, granting
// write on [foo, fop), read on [foo, foq), then write on [foo, foq) (an
// upgrade) appends the write beside the read: [W fop, R foq, W foq]. This test
// writes that role directly, then downgrades [foo, foq) to read again. The fix
// updates only the first permission on the range (the read one), so the
// stale write permission stays and the user can still write "fop".
func TestRoleGrantPermissionExistingDuplicate(t *testing.T) {
	as, tearDown := setupAuthStore(t)
	defer tearDown(t)

	_, err := as.RoleAdd(&pb.AuthRoleAddRequest{Name: "role-test-1"})
	require.NoError(t, err)
	_, err = as.UserGrantRole(&pb.AuthUserGrantRoleRequest{User: "foo", Role: "role-test-1"})
	require.NoError(t, err)

	perm := func(rangeEnd string, pt authpb.Permission_Type) *authpb.Permission {
		return &authpb.Permission{PermType: pt, Key: []byte("foo"), RangeEnd: []byte(rangeEnd)}
	}
	// the role as an etcd without the fix leaves it after the three grants above
	tx := as.be.BatchTx()
	tx.Lock()
	tx.UnsafePutRole(&authpb.Role{
		Name: []byte("role-test-1"),
		KeyPermission: []*authpb.Permission{
			perm("fop", authpb.Permission_WRITE),
			perm("foq", authpb.Permission_READ),
			perm("foq", authpb.Permission_WRITE),
		},
	})
	as.commitRevision(tx)
	as.refreshRangePermCache(tx)
	tx.Unlock()
	require.NoError(t, as.isOpPermitted("foo", as.Revision(), []byte("fop"), nil, authpb.Permission_WRITE))

	// downgrade [foo, foq) to read
	_, err = as.RoleGrantPermission(&pb.AuthRoleGrantPermissionRequest{
		Name: "role-test-1", Perm: perm("foq", authpb.Permission_READ),
	})
	require.NoError(t, err)

	r, err := as.RoleGet(&pb.AuthRoleGetRequest{Role: "role-test-1"})
	require.NoError(t, err)
	t.Logf("permissions after the downgrade: %v", r.Perm)
	require.ErrorIs(t, as.isOpPermitted("foo", as.Revision(), []byte("fop"), nil, authpb.Permission_WRITE), ErrPermissionDenied,
		"write on fop still permitted after downgrading [foo, foq) to read")
}
