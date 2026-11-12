package etcdserverreq

import (
	"context"

	pb "go.etcd.io/etcd/api/v3/etcdserverpb"
	"go.etcd.io/etcd/server/v3/etcdserver"
)

// REQ etcdserverreq/user-add-get: an added user has no roles until one is granted.
// Users: api/v3rpc/auth.go:116,132 (etcdctl user add, user get; the client's Auth API).
// Assumes: ctx's principal is an administrator (or auth is off); no other administrator changes
// user name.
// Specs: EtcdServer.UserAdd.spec, EtcdServer.UserGet.spec.
func ReqUserAddGet(ctx context.Context, s *etcdserver.EtcdServer, name string) {
	if _, err := s.UserAdd(ctx, &pb.AuthUserAddRequest{Name: name, Password: "pw"}); err != nil {
		return
	}
	resp, err := s.UserGet(ctx, &pb.AuthUserGetRequest{Name: name})
	if err != nil {
		return
	}
	if len(resp.Roles) != 0 {
		panic("user-add-get: roles out of nowhere")
	}
}

// REQ etcdserverreq/authenticate: a successful authentication returns a reply whose token names the
// user (tokenUser, which the client keeps for its later calls); with auth disabled it fails
// (ErrAuthNotEnabled).
// Users: api/v3rpc/auth.go:60 (the client's token refresh: client/v3/client.go getToken).
// Assumes: name's password is pw and stays so (no other administrator changes it).
// Specs: EtcdServer.Authenticate.spec (a persistent update: fired by the read registry);
// tokenUser.
func ReqAuthenticate(ctx context.Context, s *etcdserver.EtcdServer, name, pw string) string {
	resp, err := s.Authenticate(ctx, &pb.AuthenticateRequest{Name: name, Password: pw})
	if err != nil {
		return ""
	}
	if resp == nil {
		panic("authenticate: no reply")
	}
	return resp.Token
}

// REQ etcdserverreq/auth-status: the auth status's revision never goes back between two calls.
// Users: api/v3rpc/auth.go:52 (etcdctl auth status; the client's AuthStatus).
// Specs: EtcdServer.AuthStatus.spec; laws: etcdLb_ord, etcdState_lb.
func ReqAuthStatus(ctx context.Context, s *etcdserver.EtcdServer) {
	a, err := s.AuthStatus(ctx, &pb.AuthStatusRequest{})
	if err != nil {
		return
	}
	b, err := s.AuthStatus(ctx, &pb.AuthStatusRequest{})
	if err != nil {
		return
	}
	if b.AuthRevision < a.AuthRevision {
		panic("auth-status: revision went back")
	}
}
