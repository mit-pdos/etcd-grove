package clientv3client

import (
	"context"

	"go.etcd.io/etcd/api/v3/v3rpc/rpctypes"
	clientv3 "go.etcd.io/etcd/client/v3"
	"go.uber.org/zap"
	"google.golang.org/grpc/metadata"
)

// REQ clientv3client/admin-setup: an administrator's set-up with auth off: each call either
// succeeds, or answers a definite error the model allows for that step (a user or role that
// already exists), or settles nothing; after it, AuthEnable succeeds (root exists with the root
// role) unless an indefinite error or a refusal intervened.
// Users: examples/etcd/auth/authkv.go:298-322 (SetUp), etcdctl.
// Assumes: auth is off and no user or role exists at the start, and no other principal changes
// the auth state (the owner's invariant: the admin-history example's exclusive view).
// Specs: authClient.{UserAdd,UserGrantRole,RoleAdd,RoleGrantPermission,AuthEnable}.spec
// (Auth.methods); model: authStep.
func ReqAdminSetUp(ctx context.Context, cli *clientv3.Client, rootPw, lo, hi string) {
	if _, err := cli.Auth.UserAdd(ctx, "root", rootPw); err != nil {
		if err == rpctypes.ErrUserAlreadyExist {
			panic("admin-setup: root existed")
		}
		return
	}
	if _, err := cli.Auth.UserGrantRole(ctx, "root", "root"); err != nil {
		if err == rpctypes.ErrUserNotFound || err == rpctypes.ErrRoleNotFound {
			panic("admin-setup: root role not granted")
		}
		return
	}
	if _, err := cli.Auth.RoleAdd(ctx, "r"); err != nil {
		return
	}
	if _, err := cli.Auth.RoleGrantPermission(ctx, "r", lo, hi, clientv3.PermissionType(clientv3.PermReadWrite)); err != nil {
		if err == rpctypes.ErrRoleNotFound {
			panic("admin-setup: role lost")
		}
		return
	}
	if _, err := cli.Auth.AuthEnable(ctx); err != nil {
		if err == rpctypes.ErrRootUserNotExist || err == rpctypes.ErrRootRoleNotExist {
			panic("admin-setup: enable without root")
		}
		return
	}
}

// REQ clientv3client/user-client: a client with a user name and password authenticates as that
// user: its writes are linearized as that user's (a permission refusal is the model's
// permErr), never as another principal's; with auth on and the user unknown, New fails.
// Users: examples/etcd/auth/authkv.go:123 (newUserClient), Kubernetes with etcd auth.
// Assumes: ep serves the cluster.
// Specs: New.spec with cfgPrincipal_user, Client.Put.spec (W0: Step (some name)).
func ReqUserClient(ctx context.Context, ep, name, pw string, lg *zap.Logger) {
	cli, err := clientv3.New(clientv3.Config{Endpoints: []string{ep}, Username: name, Password: pw, Logger: lg})
	if err != nil {
		return
	}
	defer cli.Close()
	_, err = cli.Put(ctx, "k", "v")
	if err == rpctypes.ErrUserEmpty {
		// a token refusal is refreshed and resent by the interceptor; it reaches the caller only as
		// a refusal the interceptor fired (no change), never as an applied write
		return
	}
}

// REQ clientv3client/refresh-at-most-once: a write whose first attempt meets a stale token (the
// password changed, the auth revision moved) is resent only after a token refresh, and applied at
// most once: the caller's update (exclusive) fires once, whatever the interceptor did.
// Users: every write of a client with credentials (Kubernetes' writes, the concurrency recipes).
// Assumes: none. This snippet checks nothing in Go: its reliance (one firing of the put's update) is
// a ghost assertion of the owner's invariant (the update is exclusive: fired at most once by
// uiOk_call's construction), recorded here for the reviewers.
// Specs: Client.Put.spec (W0), Client.unaryClientInterceptor.spec (uiOk_call), Client.getToken.spec,
// authClient.UserChangePassword.spec.
func ReqRefreshAtMostOnce(ctx context.Context, admin, user *clientv3.Client, name, newPw string) {
	if _, err := admin.Auth.UserChangePassword(ctx, name, newPw); err != nil {
		return
	}
	// the user's client still has the old password: its next write's refresh fails with
	// ErrAuthFailed, a refusal the interceptor fires (nothing applied)
	_, err := user.Put(ctx, "k", "v")
	if err == rpctypes.ErrAuthFailed {
		return
	}
}

// REQ clientv3client/refused-principals: with auth on, a client with no credentials (anon) and the
// same client sending a token no provider issued (bad, through grpc metadata) are refused every
// write: the error is never nil. (No bundle: the interceptor resends a token refusal as is until
// its limit, then fires it as a refusal.)
// Users: examples/etcd/auth/authkv.go:151-205 (reqCtx, refused: "anon"'s and "bad"'s puts).
// Assumes: auth is on for good (the owner's invariant: no AuthDisable); badToken was never issued
// (ctxPrin of a context carrying an unissued token: requested of W0/3d,
// req/go_etcd_io_etcd_client_v3.md "from 1c (round 1)"); anon has no role on k.
// Specs: New.spec (cfgPrincipal_none), Client.Put.spec (W0), uiOk_call; model: kvStep (permErr,
// refusals).
func ReqRefusedPrincipals(ctx context.Context, anon *clientv3.Client, k, badToken string) {
	_, err := anon.Put(ctx, k, "v")
	if err == nil {
		panic("refused-principals: anon's put was not refused")
	}
	bctx := metadata.AppendToOutgoingContext(ctx, "token", badToken)
	_, err = anon.Put(bctx, k, "v")
	if err == nil {
		panic("refused-principals: bad's put was not refused")
	}
}
