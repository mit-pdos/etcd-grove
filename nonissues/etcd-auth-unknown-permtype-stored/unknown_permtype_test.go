package auth

import (
	"errors"
	"testing"

	"go.etcd.io/etcd/api/v3/authpb"
	pb "go.etcd.io/etcd/api/v3/etcdserverpb"
)

// Two roles the model sees as the same (no permission), RoleRevokePermission differing.
func TestD3RevokeUnknownTypedPermission(t *testing.T) {
	as, tearDown := setupAuthStore(t)
	defer tearDown(t)
	for _, n := range []string{"r-unknown", "r-empty"} {
		if _, err := as.RoleAdd(&pb.AuthRoleAddRequest{Name: n}); err != nil {
			t.Fatal(err)
		}
	}
	if _, err := as.RoleGrantPermission(&pb.AuthRoleGrantPermissionRequest{Name: "r-unknown",
		Perm: &authpb.Permission{PermType: authpb.Permission_Type(7), Key: []byte("k")}}); err != nil {
		t.Fatalf("grant of an unknown type refused: %v", err)
	}
	rev := as.Revision()
	if _, err := as.RoleRevokePermission(&pb.AuthRoleRevokePermissionRequest{Role: "r-unknown", Key: []byte("k")}); err != nil {
		t.Fatalf("revoke on r-unknown: %v", err)
	}
	if as.Revision() != rev+1 {
		t.Fatalf("revision %d, want %d", as.Revision(), rev+1)
	}
	rev = as.Revision()
	_, err := as.RoleRevokePermission(&pb.AuthRoleRevokePermissionRequest{Role: "r-empty", Key: []byte("k")})
	if !errors.Is(err, ErrPermissionNotGranted) || as.Revision() != rev {
		t.Fatalf("revoke on r-empty: %v, revision %d (was %d)", err, as.Revision(), rev)
	}
}
