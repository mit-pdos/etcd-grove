package auth

import (
	"testing"

	"go.etcd.io/etcd/api/v3/authpb"
	pb "go.etcd.io/etcd/api/v3/etcdserverpb"
)

// TestRoleGrantPermissionSameKeyNoUpdate: granting a permission on a range the role already has
// does not update it when another permission with the same key sorts before it; the new one is
// appended and the old type stays in effect (a "downgrade" to READ leaves WRITE granted).
func TestRoleGrantPermissionSameKeyNoUpdate(t *testing.T) {
	as, tearDown := setupAuthStore(t)
	defer tearDown(t)

	grant := func(key, end string, ty authpb.Permission_Type) {
		_, err := as.RoleGrantPermission(&pb.AuthRoleGrantPermissionRequest{
			Name: "role-test",
			Perm: &authpb.Permission{PermType: ty, Key: []byte(key), RangeEnd: []byte(end)},
		})
		if err != nil {
			t.Fatal(err)
		}
	}
	grant("a", "", authpb.READ)
	grant("a", "c", authpb.READWRITE)
	// Downgrade [a, c) to READ.
	grant("a", "c", authpb.READ)

	r, err := as.RoleGet(&pb.AuthRoleGetRequest{Role: "role-test"})
	if err != nil {
		t.Fatal(err)
	}
	for _, p := range r.Perm {
		t.Logf("perm %q %q %v", p.Key, p.RangeEnd, p.PermType)
	}
	if _, err := as.UserGrantRole(&pb.AuthUserGrantRoleRequest{User: "foo", Role: "role-test"}); err != nil {
		t.Fatal(err)
	}
	ai := &AuthInfo{Username: "foo", Revision: as.Revision()}
	if err := as.IsPutPermitted(ai, []byte("b")); err == nil {
		t.Errorf("put of b permitted after [a, c) was set to READ (%d permissions)", len(r.Perm))
	}
}
