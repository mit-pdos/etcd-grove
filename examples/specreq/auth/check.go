// Package auth holds the requirement snippets of etcd's auth store (batch 3d,
// Spec/go_etcd_io/etcd/server/v3/auth/): what its callers (the apply layer, the request path,
// the gRPC handlers, the watch server, the server's boot and snapshot install) rely on.
package auth

import (
	"context"
	"errors"

	etcdauth "go.etcd.io/etcd/server/v3/auth"
)

// REQ auth/check-pass: a permission check that passes is justified at one state the cluster
// reached: auth off there, or the user of the root role, or the range covered by its roles. A
// read-only check never panics, whatever the request's key range (an inverted one included).
// Users: server/etcdserver/v3_server.go:146 (Range's chk), api/v3rpc/watch.go:248
// (isWatchPermitted), v3_server.go:595,627 (the lease checks).
// Assumes: ai is AuthInfoFromCtx's answer for the request (or &AuthInfo{}); the keys are a
// decoded request's (bounded).
// Specs: authStore.IsRangePermitted.spec (checkPost, checkOk), authAt_reached; the caller turns
// checkOk at the recorded state into State.permits (W0).
func ReqCheckPass(as etcdauth.AuthStore, ai *etcdauth.AuthInfo, key, rangeEnd []byte) bool {
	err := as.IsRangePermitted(ai, key, rangeEnd)
	if err == nil {
		return true
	}
	if !errors.Is(err, etcdauth.ErrUserEmpty) && !errors.Is(err, etcdauth.ErrAuthOldRevision) &&
		!errors.Is(err, etcdauth.ErrPermissionDenied) {
		panic("check-pass: an error a permission check does not return")
	}
	return false
}

// REQ auth/no-user: with no credentials (the empty AuthInfo doSerialize passes), a check passes
// only where auth is off; with auth on it is ErrUserEmpty, never a pass for a user's roles.
// Users: v3_server.go:1043 (doSerialize's &auth.AuthInfo{}).
// Assumes: auth stays enabled (the caller's workload: no AuthDisable during the call).
// Specs: authStore.IsRangePermitted.spec (checkOk with rev = 0), IsAuthEnabled.spec.
func ReqNoUser(as etcdauth.AuthStore, key []byte) {
	if !as.IsAuthEnabled() {
		return
	}
	err := as.IsRangePermitted(&etcdauth.AuthInfo{}, key, nil)
	if err == nil {
		panic("no-user: a check passed without a user while auth is on")
	}
}

// REQ auth/writer-check: the apply thread's check (the store's only writer) answers at the
// store's current state: a pass is that state's permission, a denial its refusal; the write
// check of a key and the administrator check agree with W0's permits and admin there.
// Users: apply/auth.go:53,74,104,215,223,235 (the auth applier's checks, HasRole).
// Assumes: called by the apply thread between two admin steps (it holds authCur, and the
// backend's post-lock hook for HasRole's batch lock: authHook).
// Specs: authStore.IsPutPermitted.spec (checkPost's ErrAuthOldRevision: rev below the store's),
// IsAdminPermitted.spec, HasRole.spec, Revision.spec; laws: authCur_at, authAt_le, authAt_agree.
func ReqWriterCheck(as etcdauth.AuthStore, user string, rev uint64, key []byte) {
	ai := &etcdauth.AuthInfo{Username: user, Revision: rev}
	admin := as.IsAdminPermitted(ai) == nil
	put := as.IsPutPermitted(ai, key)
	if admin && as.IsAuthEnabled() && rev != 0 && rev >= as.Revision() && put != nil {
		panic("writer-check: an administrator refused a write at the same state")
	}
	_ = as.HasRole(user, "root")
}

// REQ auth/admin-check: the administrator check returns nil, or one of its three refusals.
// Users: server.go:1403 (checkMembershipOperationPermission), api/v3rpc/auth.go:188 (AuthAdmin),
// v3_server.go:588 (the lease checks).
// Specs: authStore.IsAdminPermitted.spec (adminPost).
func ReqAdminCheck(as etcdauth.AuthStore, ai *etcdauth.AuthInfo) {
	err := as.IsAdminPermitted(ai)
	if err != nil && !errors.Is(err, etcdauth.ErrUserEmpty) && !errors.Is(err, etcdauth.ErrUserNotFound) &&
		!errors.Is(err, etcdauth.ErrPermissionDenied) {
		panic("admin-check: an error IsAdminPermitted does not return")
	}
}

// REQ auth/enabled-flag: requireAuthInfo's pattern: auth off at a reached state, or a request
// with no credentials refused.
// Users: v3_server.go:1278 (requireAuthInfo), api/v3rpc/auth.go:192.
// Specs: authStore.IsAuthEnabled.spec, AuthInfoFromCtx.spec.
func ReqEnabledFlag(ctx context.Context, as etcdauth.AuthStore) error {
	if !as.IsAuthEnabled() {
		return nil
	}
	ai, err := as.AuthInfoFromCtx(ctx)
	if err != nil {
		if !errors.Is(err, etcdauth.ErrInvalidAuthToken) {
			panic("enabled-flag: AuthInfoFromCtx's only error is ErrInvalidAuthToken")
		}
		return err
	}
	if ai == nil {
		return etcdauth.ErrUserEmpty
	}
	return nil
}
