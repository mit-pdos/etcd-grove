package auth

import (
	"context"
	"errors"

	pb "go.etcd.io/etcd/api/v3/etcdserverpb"
	etcdauth "go.etcd.io/etcd/server/v3/auth"
)

// REQ auth/token-user: a request's token is mapped to the user the cluster issued it to (W0's
// tokenUser), or refused (ErrInvalidAuthToken: expired, invalidated, a token of another
// member's simple provider); with auth off or no token, no credentials.
// Users: v3_server.go:1207 (EtcdServer.AuthInfoFromCtx), through it every request's principal.
// Assumes: ctx is a gRPC run's context whose metadata carries tok, which the cluster issued to
// user (the client's interceptor attaches the token Authenticate returned).
// Specs: authStore.AuthInfoFromCtx.spec (ctxToken over grpc's ctxInMD, tokKeysOk by
// Grpc.rpcCtx_vals; authGate γa R with □ R: the server started; tokenUser); W0's tokenUser_agree.
func ReqTokenUser(ctx context.Context, as etcdauth.AuthStore, user string) {
	ai, err := as.AuthInfoFromCtx(ctx)
	if err != nil {
		if !errors.Is(err, etcdauth.ErrInvalidAuthToken) {
			panic("token-user: an error AuthInfoFromCtx does not return")
		}
		return
	}
	if ai != nil && ai.Username != user {
		panic("token-user: a token mapped to another user")
	}
}

// REQ auth/no-token: a context with no auth metadata (the server's own s.ctx, an internal
// requester's) has no credentials, at every mode.
// Users: v3_server.go:1067 (processInternalRaftRequestOnce from the lessor, the compactor).
// Assumes: ctx carries no incoming metadata.
// Specs: authStore.AuthInfoFromCtx.spec (ctxToken ctx none).
func ReqNoToken(ctx context.Context, as etcdauth.AuthStore) {
	ai, err := as.AuthInfoFromCtx(ctx)
	if err != nil || ai != nil {
		panic("no-token: credentials out of nowhere")
	}
}

// REQ auth/cert-user: with client-certificate authentication, a request with no token is the
// certificate's common name's (or none, with no verified TLS peer).
// Users: v3_server.go:1214 (EtcdServer.AuthInfoFromCtx's fallback).
// Assumes: ctx's TLS identity is cn (a verified chain whose leaf's common name is cn, no
// grpcgateway-accept header).
// Specs: authStore.AuthInfoFromTLS.spec (ctxCertUser).
func ReqCertUser(ctx context.Context, as etcdauth.AuthStore, cn string) {
	ai := as.AuthInfoFromTLS(ctx)
	if ai == nil || ai.Username != cn {
		panic("cert-user: not the certificate's user")
	}
}

// REQ auth/with-root: the lessor's revocation context is root's when auth is on: the store's
// AuthInfoFromCtx on it names root (or refuses it, or finds auth off).
// Users: server.go:881 (revokeExpiredLeases: s.LeaseRevoke(s.authStore.WithRoot(s.ctx), ...)).
// Assumes: the provider is not the simple one (rootTokOk; the simple provider's root tokens may
// collide: nonissues/etcd-auth-withroot-token-collision-panic.md); ctx carries no metadata.
// Specs: authStore.WithRoot.spec, AuthInfoFromCtx.spec; W0's tokenUser_agree.
func ReqWithRoot(ctx context.Context, as etcdauth.AuthStore) {
	rctx := as.WithRoot(ctx)
	ai, err := as.AuthInfoFromCtx(rctx)
	if err == nil && ai != nil && ai.Username != "root" {
		panic("with-root: a root context naming another user")
	}
}

// REQ auth/authenticate-apply: the apply of an InternalAuthenticateRequest at entry index idx,
// whose context carries the index and the proposer's prefix, answers auth off, an error, or a
// token the cluster issued to the user (which every later AuthInfoFromCtx maps to that user).
// Users: apply/backend.go:159 (applierV3backend.Authenticate), v3_server.go:865 (the prefix).
// Assumes: the apply thread, at the entry's index (above every earlier one), with the entry's
// prefix; the cluster issued prefix.idx to name (2d's realization of tokenUser).
// Specs: authStore.Authenticate.spec (authnCtx, tokFrom), GenTokenPrefix.spec.
func ReqAuthenticateApply(ctx context.Context, as etcdauth.AuthStore, idx uint64, name string) *pb.AuthenticateResponse {
	prefix, err := as.GenTokenPrefix()
	if err != nil {
		return nil
	}
	actx := context.WithValue(context.WithValue(ctx, etcdauth.AuthenticateParamIndex{}, idx),
		etcdauth.AuthenticateParamSimpleTokenPrefix{}, prefix)
	resp, err := as.Authenticate(actx, name, "")
	if err != nil {
		return nil
	}
	if resp == nil {
		panic("authenticate-apply: no response")
	}
	return resp
}
