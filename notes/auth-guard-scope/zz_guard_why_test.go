// Copy into server/etcdserver at the etcd fork pin 2eaeb872b beside zz_guard_etcdserver_test.go
// (whose zzgSetup, zzgCtx and zzgIs it uses; notes/auth-guard-scope.md, section 4) and run
// `GOWORK=off go test ./etcdserver/ -run TestZZGuardWhy -v` in server/.
//
// The revised G2 reasons (auth-guard-completeness, 2026-11-14):
//   - every refusal of the guards follows a read of the enabled flag `true` during the call: with auth
//     disabled, no guard refuses, whatever the context (no token, a token the provider never issued);
//     the regression shape the reasons exclude is a guard that refuses without that read
//     (zzgNoFlagRequireAuthInfo: requireAuthInfo without its IsAuthEnabled check refuses with
//     ErrUserEmpty on an auth-disabled cluster);
//   - IsAdminPermitted's errors are tied to their cases (store.go:916-933): ErrUserEmpty only for a nil
//     or unnamed auth info, ErrUserNotFound only for a named user absent from the store,
//     ErrPermissionDenied only for a present user without the root role.
package etcdserver

import (
	"context"
	"testing"

	"go.etcd.io/etcd/server/v3/auth"
)

// zzgNoFlagRequireAuthInfo: requireAuthInfo with its `IsAuthEnabled()` check dropped (a guard that
// refuses without reading the flag `true`).
func zzgNoFlagRequireAuthInfo(s *EtcdServer, ctx context.Context) error {
	authInfo, err := s.AuthInfoFromCtx(ctx)
	if err != nil {
		return err
	}
	if authInfo == nil {
		return auth.ErrUserEmpty
	}
	return nil
}

func TestZZGuardWhyAuthDisabled(t *testing.T) {
	as, _, toks := zzgSetup(t)
	s := &EtcdServer{authStore: as}
	as.AuthDisable()
	for name, ctx := range map[string]context.Context{
		"no token":     zzgCtx(""),
		"bad token":    zzgCtx("pfx.99"),
		"u's token":    zzgCtx(toks["u"]),
		"root's token": zzgCtx(toks["root"]),
	} {
		zzgIs(t, "off: requireAuthInfo("+name+")", s.requireAuthInfo(ctx), nil)
		zzgIs(t, "off: checkMembershipOperationPermission("+name+")",
			s.checkMembershipOperationPermission(ctx), nil)
		ai, err := as.AuthInfoFromCtx(ctx)
		if ai != nil || err != nil {
			t.Errorf("off: AuthInfoFromCtx(%s) = (%v, %v), want (nil, nil)", name, ai, err)
		}
	}
	zzgIs(t, "off: IsAdminPermitted(nil)", as.IsAdminPermitted(nil), nil)
	zzgIs(t, "off: IsAdminPermitted(u)", as.IsAdminPermitted(&auth.AuthInfo{Username: "u", Revision: 1}), nil)
	// the regression shape: a guard that refuses without reading the flag `true`
	zzgIs(t, "off: requireAuthInfo without its flag check (no token)",
		zzgNoFlagRequireAuthInfo(s, zzgCtx("")), auth.ErrUserEmpty)
}

func TestZZGuardWhyAdminErrorCases(t *testing.T) {
	as, _, _ := zzgSetup(t)
	rev := as.Revision()
	zzgIs(t, "IsAdminPermitted(nil)", as.IsAdminPermitted(nil), auth.ErrUserEmpty)
	zzgIs(t, "IsAdminPermitted(unnamed)", as.IsAdminPermitted(&auth.AuthInfo{Username: "", Revision: rev}),
		auth.ErrUserEmpty)
	zzgIs(t, "IsAdminPermitted(absent user)",
		as.IsAdminPermitted(&auth.AuthInfo{Username: "ghost", Revision: rev}), auth.ErrUserNotFound)
	zzgIs(t, "IsAdminPermitted(u, not root)", as.IsAdminPermitted(&auth.AuthInfo{Username: "u", Revision: rev}),
		auth.ErrPermissionDenied)
	zzgIs(t, "IsAdminPermitted(v, no role)", as.IsAdminPermitted(&auth.AuthInfo{Username: "v", Revision: rev}),
		auth.ErrPermissionDenied)
	zzgIs(t, "IsAdminPermitted(root)", as.IsAdminPermitted(&auth.AuthInfo{Username: "root", Revision: rev}), nil)
	// the server's guard: each refusal's error is its case's
	s := &EtcdServer{authStore: as}
	zzgIs(t, "checkMembershipOperationPermission(no token)", s.checkMembershipOperationPermission(zzgCtx("")),
		auth.ErrUserEmpty)
	zzgIs(t, "checkMembershipOperationPermission(bad token)",
		s.checkMembershipOperationPermission(zzgCtx("pfx.99")), auth.ErrInvalidAuthToken)
}
