package auth

import (
	"encoding/base64"
	"errors"

	"golang.org/x/crypto/bcrypt"

	"go.etcd.io/etcd/api/v3/authpb"
	pb "go.etcd.io/etcd/api/v3/etcdserverpb"
	etcdauth "go.etcd.io/etcd/server/v3/auth"
)

// REQ auth/admin-steps: the apply thread's admin steps are W0's authStep effects at the store's
// state, each recorded as the store's next state, with the model's errors: a role added then
// granted to a new user; deleting a missing user fails with ErrUserNotFound; the root user
// cannot be deleted while auth is on.
// Users: apply/backend.go:139-263 (applierV3backend's auth methods), behind apply/auth.go:52.
// Assumes: the apply thread, the store's only writer (authCur); each step is the committed
// entry's (its one next state, storeNext, reached; its records fit); hashed is b64 of a hash of
// some password (W0's pwHash); no user "u" or role "r" before; name "nobody" never added; the
// backend's post-lock hook for each batch lock (authHook: the applier's, from the apply loop).
// Specs: authStore.{RoleAdd,UserAdd,UserGrantRole,UserGet,HasRole,UserDelete,RoleGrantPermission,
// AuthEnable,AuthDisable,IsAuthEnabled}.spec
// (AdminTriple, storeNext, admStep); laws: authCur_at.
func ReqAdminSteps(as etcdauth.AuthStore, hashed string) {
	if _, err := as.RoleAdd(&pb.AuthRoleAddRequest{Name: "r"}); err != nil {
		panic("admin-steps: adding a new role failed")
	}
	if _, err := as.UserAdd(&pb.AuthUserAddRequest{Name: "u", HashedPassword: hashed}); err != nil {
		panic("admin-steps: adding a new user failed")
	}
	if _, err := as.UserGrantRole(&pb.AuthUserGrantRoleRequest{User: "u", Role: "r"}); err != nil {
		panic("admin-steps: granting an existing role to an existing user failed")
	}
	if _, err := as.UserGet(&pb.AuthUserGetRequest{Name: "u"}); err != nil {
		panic("admin-steps: an existing user not found")
	}
	if !as.HasRole("u", "r") {
		panic("admin-steps: the granted role is not the user's")
	}
	if _, err := as.UserDelete(&pb.AuthUserDeleteRequest{Name: "nobody"}); !errors.Is(err, etcdauth.ErrUserNotFound) {
		panic("admin-steps: deleting a missing user did not fail with ErrUserNotFound")
	}
	if _, err := as.RoleGrantPermission(&pb.AuthRoleGrantPermissionRequest{Name: "r",
		Perm: &authpb.Permission{PermType: authpb.Permission_READ, Key: []byte("k")}}); err != nil {
		panic("admin-steps: a valid grant to an existing role failed")
	}
	if as.AuthEnable() == nil && as.IsAuthEnabled() {
		if _, err := as.UserDelete(&pb.AuthUserDeleteRequest{Name: "root"}); !errors.Is(err, etcdauth.ErrInvalidAuthMgmt) {
			panic("admin-steps: root deleted while auth is on")
		}
		as.AuthDisable()
	}
}

// REQ auth/user-add-then-check: a user added with the hash of pw (the proposer's form) passes
// CheckPassword with pw while auth is on, at the revision of the state it read; a password-less
// user never passes.
// Users: v3_server.go:893 (EtcdServer.UserAdd hashes and encodes), :853 (Authenticate's
// CheckPassword); apply/backend.go:167.
// Assumes: the apply thread adds the user (no user "v" before; the post-lock hook, authHook);
// auth is on and stays on, and no
// other step changes "v" (the caller's workload); pw at most 72 bytes.
// Specs: bcrypt GenerateFromPassword.spec, CompareHashAndPassword.spec; W0's pwHash_match;
// authStore.BcryptCost.spec, UserAdd.spec, CheckPassword.spec.
func ReqUserAddThenCheck(as etcdauth.AuthStore, pw string) {
	h, err := bcrypt.GenerateFromPassword([]byte(pw), as.BcryptCost())
	if err != nil {
		panic("user-add-then-check: hashing a short password with the store's cost failed")
	}
	r := &pb.AuthUserAddRequest{Name: "v", HashedPassword: base64.StdEncoding.EncodeToString(h)}
	if _, err := as.UserAdd(r); err != nil {
		panic("user-add-then-check: adding a new user failed")
	}
	if _, err := as.CheckPassword("v", pw); err != nil && !errors.Is(err, etcdauth.ErrAuthNotEnabled) {
		panic("user-add-then-check: the user's own password refused")
	}
}

// REQ auth/long-password: the server hashes a password before proposing it; one over 72 bytes is
// refused with bcrypt's ErrPasswordTooLong (whatever the cost), which UserAdd returns to the
// client as an unmapped error (its message).
// Users: v3_server.go:893,918 (EtcdServer.UserAdd, UserChangePassword).
// Assumes: len(pw) > 72.
// Specs: bcrypt GenerateFromPassword.spec (errIs ErrPasswordTooLong), bcrypt init.spec.
func ReqLongPassword(as etcdauth.AuthStore, pw []byte) error {
	_, err := bcrypt.GenerateFromPassword(pw, as.BcryptCost())
	if !errors.Is(err, bcrypt.ErrPasswordTooLong) {
		panic("long-password: a password over 72 bytes not refused with ErrPasswordTooLong")
	}
	return err
}

// REQ auth/revision-bumped: an admin step that changes the users or roles bumps the revision:
// a reader's two equal Revision() reads mean no such change between the states they read.
// Users: v3_server.go:881 (Authenticate's retry), :601,:779 (the lease checks' re-check),
// apply/backend.go:153 (AuthStatus).
// Assumes: the apply thread adds a new role between the two reads (with the post-lock hook).
// Specs: authStore.Revision.spec, RoleAdd.spec; laws: authAt_reach (and W0's authStep bumps).
func ReqRevisionBumped(as etcdauth.AuthStore) {
	r0 := as.Revision()
	if _, err := as.RoleAdd(&pb.AuthRoleAddRequest{Name: "fresh-role"}); err != nil {
		return
	}
	if as.Revision() == r0 {
		panic("revision-bumped: a role added without bumping the revision")
	}
}
