// Copy into server/etcdserver at the etcd fork pin 2eaeb872b (notes/auth-guard-scope.md, section 4)
// and run `GOWORK=off go test ./etcdserver/ -run TestZZGuard -v` in server/.
//
// The converse of the server's auth guards ("a request whose principal the class admits is not
// refused by the guard"), per class, on a real auth store with the simple token provider:
//   - authenticated (requireAuthInfo): every accepted token passes; the only refusals are
//     ErrUserEmpty for a context with no token and ErrInvalidAuthToken for a token the provider
//     does not hold;
//   - admin (checkMembershipOperationPermission): root's token passes; a non-root token is refused
//     with ErrPermissionDenied, a context with no token with ErrUserEmpty;
//   - the lease checks (RBAC: admin, or every key of the lease): a permitted principal passes.
// And the fail-closed regressions the converse excludes:
//   - 3.6.9's MemberList (GHSA-q8m4-xhhv-38mg's fix a07ecd124, reverted to requireAuthInfo by
//     etcd-io/etcd#21538): the admin guard in place of requireAuthInfo refuses a non-root user's
//     accepted token with ErrPermissionDenied, a refusal the authenticated class does not allow;
//   - etcd-io/etcd#20757 (before 37531e62f): the leader's context lost the follower's token; the
//     admin guard then refuses root with ErrUserEmpty. The guard's converse holds there (ErrUserEmpty
//     only for a context with no token): what breaks is the forwarding, which
//     zz_guard_promote_test.go checks.
package etcdserver

import (
	"context"
	"errors"
	"net/http"
	"net/http/httptest"
	"testing"
	"time"

	"go.uber.org/zap/zaptest"
	"golang.org/x/crypto/bcrypt"
	"google.golang.org/grpc/metadata"

	"go.etcd.io/etcd/api/v3/authpb"
	pb "go.etcd.io/etcd/api/v3/etcdserverpb"
	"go.etcd.io/etcd/api/v3/v3rpc/rpctypes"
	"go.etcd.io/etcd/server/v3/auth"
	"go.etcd.io/etcd/server/v3/lease"
	"go.etcd.io/etcd/server/v3/storage/backend"
	betesting "go.etcd.io/etcd/server/v3/storage/backend/testing"
	"go.etcd.io/etcd/server/v3/storage/schema"
)

// zzgSetup: an auth store with auth enabled; root (role root), u (role r: read "a", readwrite
// "w"), v (no role); one simple token each, issued as the apply thread does (index, prefix).
func zzgSetup(t *testing.T) (auth.AuthStore, backend.Backend, map[string]string) {
	lg := zaptest.NewLogger(t)
	be, _ := betesting.NewDefaultTmpBackend(t)
	t.Cleanup(func() { betesting.Close(t, be) })
	ready := make(chan struct{})
	close(ready)
	tp, err := auth.NewTokenProvider(lg, "simple", func(uint64) <-chan struct{} { return ready }, 5*time.Minute)
	if err != nil {
		t.Fatal(err)
	}
	as := auth.NewAuthStore(lg, schema.NewAuthBackend(lg, be), tp, bcrypt.MinCost)
	must := func(_ any, err error) {
		t.Helper()
		if err != nil {
			t.Fatal(err)
		}
	}
	for _, u := range []string{"root", "u", "v"} {
		must(as.UserAdd(&pb.AuthUserAddRequest{Name: u, Password: "pw"}))
	}
	must(as.RoleAdd(&pb.AuthRoleAddRequest{Name: "root"}))
	must(as.RoleAdd(&pb.AuthRoleAddRequest{Name: "r"}))
	must(as.RoleGrantPermission(&pb.AuthRoleGrantPermissionRequest{Name: "r",
		Perm: &authpb.Permission{PermType: authpb.READ, Key: []byte("a")}}))
	must(as.RoleGrantPermission(&pb.AuthRoleGrantPermissionRequest{Name: "r",
		Perm: &authpb.Permission{PermType: authpb.READWRITE, Key: []byte("w")}}))
	must(as.UserGrantRole(&pb.AuthUserGrantRoleRequest{User: "root", Role: "root"}))
	must(as.UserGrantRole(&pb.AuthUserGrantRoleRequest{User: "u", Role: "r"}))
	if err := as.AuthEnable(); err != nil {
		t.Fatal(err)
	}
	toks := map[string]string{}
	for i, u := range []string{"root", "u", "v"} {
		ctx := context.WithValue(context.WithValue(context.Background(),
			auth.AuthenticateParamIndex{}, uint64(i+1)), auth.AuthenticateParamSimpleTokenPrefix{}, "pfx")
		resp, err := as.Authenticate(ctx, u, "")
		if err != nil {
			t.Fatal(err)
		}
		toks[u] = resp.Token
	}
	return as, be, toks
}

func zzgCtx(tok string) context.Context {
	if tok == "" {
		return context.Background()
	}
	return metadata.NewIncomingContext(context.Background(),
		metadata.New(map[string]string{rpctypes.TokenFieldNameGRPC: tok}))
}

func zzgIs(t *testing.T, what string, err, want error) {
	t.Helper()
	if !errors.Is(err, want) && !(err == nil && want == nil) {
		t.Errorf("%s: got %v, want %v", what, err, want)
	}
}

func TestZZGuardAuthenticated(t *testing.T) {
	as, _, toks := zzgSetup(t)
	s := &EtcdServer{authStore: as}
	// served: every principal with an accepted token, root or not, with roles or not
	for _, u := range []string{"root", "u", "v"} {
		zzgIs(t, "requireAuthInfo("+u+")", s.requireAuthInfo(zzgCtx(toks[u])), nil)
	}
	// the only refusals: no token, or a token the provider does not hold
	zzgIs(t, "requireAuthInfo(no token)", s.requireAuthInfo(zzgCtx("")), auth.ErrUserEmpty)
	zzgIs(t, "requireAuthInfo(bad token)", s.requireAuthInfo(zzgCtx("pfx.99")), auth.ErrInvalidAuthToken)
	// with auth off, never a refusal
	as.AuthDisable()
	zzgIs(t, "requireAuthInfo(off, no token)", s.requireAuthInfo(zzgCtx("")), nil)
}

func TestZZGuardAdmin(t *testing.T) {
	as, _, toks := zzgSetup(t)
	s := &EtcdServer{authStore: as}
	zzgIs(t, "admin(root)", s.checkMembershipOperationPermission(zzgCtx(toks["root"])), nil)
	// refusals name a reason the class allows: a principal without the root role, or none
	zzgIs(t, "admin(u)", s.checkMembershipOperationPermission(zzgCtx(toks["u"])), auth.ErrPermissionDenied)
	zzgIs(t, "admin(no token)", s.checkMembershipOperationPermission(zzgCtx("")), auth.ErrUserEmpty)
	zzgIs(t, "admin(bad token)", s.checkMembershipOperationPermission(zzgCtx("pfx.99")), auth.ErrInvalidAuthToken)
	// a principal granted root later is served from then on (the converse is about the state at
	// the check, not at the token's issue)
	if _, err := as.UserGrantRole(&pb.AuthUserGrantRoleRequest{User: "v", Role: "root"}); err != nil {
		t.Fatal(err)
	}
	ctx := context.WithValue(context.WithValue(context.Background(),
		auth.AuthenticateParamIndex{}, uint64(10)), auth.AuthenticateParamSimpleTokenPrefix{}, "pfx")
	resp, err := as.Authenticate(ctx, "v", "")
	if err != nil {
		t.Fatal(err)
	}
	zzgIs(t, "admin(v, now root)", s.checkMembershipOperationPermission(zzgCtx(resp.Token)), nil)
}

// memberList369 is EtcdServer.MemberList's guard as 3.6.9 shipped it (a07ecd124, the GHSA-q8m4 fix:
// checkMembershipOperationPermission), before etcd-io/etcd#21538 made it requireAuthInfo again.
func (s *EtcdServer) memberList369Guard(ctx context.Context) error {
	return s.checkMembershipOperationPermission(ctx)
}

func TestZZGuardMemberList369Regression(t *testing.T) {
	as, _, toks := zzgSetup(t)
	s := &EtcdServer{authStore: as}
	ctx := zzgCtx(toks["u"])
	// u's token is accepted (the authenticated class admits u) ...
	if ai, err := s.AuthInfoFromCtx(ctx); err != nil || ai == nil || ai.Username != "u" {
		t.Fatalf("AuthInfoFromCtx(u) = %v, %v", ai, err)
	}
	zzgIs(t, "MemberList guard at the pin", s.requireAuthInfo(ctx), nil)
	// ... and 3.6.9's guard refuses it with a reason outside the class's: the converse fails
	err := s.memberList369Guard(ctx)
	if !errors.Is(err, auth.ErrPermissionDenied) {
		t.Fatalf("3.6.9 guard: got %v, want ErrPermissionDenied", err)
	}
	t.Logf("3.6.9 MemberList guard refuses an authenticated user: %v (violates the converse)", err)
}

func TestZZGuardLeaseChecks(t *testing.T) {
	as, be, toks := zzgSetup(t)
	lg := zaptest.NewLogger(t)
	le := lease.NewLessor(lg, be, nil, lease.LessorConfig{MinLeaseTTL: 10})
	defer le.Stop()
	lw, err := le.Grant(1, 60) // holds "w": u may write and read it
	if err != nil {
		t.Fatal(err)
	}
	if err := le.Attach(lw.ID, []lease.LeaseItem{{Key: "w"}}); err != nil {
		t.Fatal(err)
	}
	lx, err := le.Grant(2, 60) // holds "x": u may not
	if err != nil {
		t.Fatal(err)
	}
	if err := le.Attach(lx.ID, []lease.LeaseItem{{Key: "x"}}); err != nil {
		t.Fatal(err)
	}
	s := &EtcdServer{authStore: as, lessor: le}
	u := zzgCtx(toks["u"])
	zzgIs(t, "checkLeaseRenew(u, w)", s.checkLeaseRenew(u, lw.ID), nil)
	_, err = s.checkLeaseTimeToLive(u, lw.ID)
	zzgIs(t, "checkLeaseTimeToLive(u, w)", err, nil)
	zzgIs(t, "checkLeaseLeases(u, [w])", s.checkLeaseLeases(u, []*lease.Lease{lw}), nil)
	// root: admin passes whatever the keys
	r := zzgCtx(toks["root"])
	zzgIs(t, "checkLeaseRenew(root, x)", s.checkLeaseRenew(r, lx.ID), nil)
	// refusals: a key u may not write or read
	zzgIs(t, "checkLeaseRenew(u, x)", s.checkLeaseRenew(u, lx.ID), auth.ErrPermissionDenied)
	_, err = s.checkLeaseTimeToLive(u, lx.ID)
	zzgIs(t, "checkLeaseTimeToLive(u, x)", err, auth.ErrPermissionDenied)
	// a lease that does not exist has no keys: served
	zzgIs(t, "checkLeaseRenew(u, missing)", s.checkLeaseRenew(u, 77), nil)
}

// The follower's half of the forwarded promotion (cluster_util.go, promoteMemberHTTP; the fix
// 37531e62f of etcd-io/etcd#20757): the request to the leader carries the token of the follower's
// gRPC context, so the leader's guard checks the same principal (the leader's half:
// zz_guard_promote_test.go). Before the fix the header was not set.
func TestZZGuardPromoteForwardsToken(t *testing.T) {
	_, _, toks := zzgSetup(t)
	got := make(chan string, 1)
	srv := httptest.NewServer(http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
		got <- r.Header.Get("Authorization")
		w.WriteHeader(http.StatusOK)
		w.Write([]byte("[]"))
	}))
	defer srv.Close()
	if _, err := promoteMemberHTTP(zzgCtx(toks["root"]), srv.URL, 1, http.DefaultTransport); err != nil {
		t.Fatal(err)
	}
	if h := <-got; h != toks["root"] {
		t.Fatalf("forwarded Authorization = %q, want root's token %q", h, toks["root"])
	}
}
