// Copy into server/etcdserver/api/v3rpc at the etcd fork pin 2eaeb872b (notes/auth-guard-scope.md,
// section 4) and run `GOWORK=off go test ./etcdserver/api/v3rpc/ -run TestZZGuard -v` in server/.
//
// The converse of the gRPC layer's guards on a real auth store with the simple token provider:
// AuthAdmin.requireAuthInfo (Status, Alarm GET), AuthAdmin.isPermitted (Compact, the maintenance
// admin rows, Alarm ACTIVATE/DEACTIVATE) and serverWatchStream.isWatchPermitted (RBAC read of the
// watched range); and that togRPCError keeps the refusal's reason (each auth error has its own
// gRPC error), so an entry point's spec can state the reason of the error the client sees.
package v3rpc

import (
	"context"
	"errors"
	"testing"
	"time"

	"go.uber.org/zap/zaptest"
	"golang.org/x/crypto/bcrypt"
	"google.golang.org/grpc/metadata"

	"go.etcd.io/etcd/api/v3/authpb"
	pb "go.etcd.io/etcd/api/v3/etcdserverpb"
	"go.etcd.io/etcd/api/v3/v3rpc/rpctypes"
	"go.etcd.io/etcd/server/v3/auth"
	betesting "go.etcd.io/etcd/server/v3/storage/backend/testing"
	"go.etcd.io/etcd/server/v3/storage/schema"
)

// zzgGetter is the server's AuthGetter as EtcdServer implements it with ClientCertAuthEnabled off
// (v3_server.go, AuthInfoFromCtx).
type zzgGetter struct{ as auth.AuthStore }

func (g zzgGetter) AuthInfoFromCtx(ctx context.Context) (*auth.AuthInfo, error) {
	return g.as.AuthInfoFromCtx(ctx)
}
func (g zzgGetter) AuthStore() auth.AuthStore { return g.as }

type zzgStream struct {
	pb.Watch_WatchServer
	ctx context.Context
}

func (s zzgStream) Context() context.Context { return s.ctx }

func zzgSetup(t *testing.T) (auth.AuthStore, map[string]string) {
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
		Perm: &authpb.Permission{PermType: authpb.READ, Key: []byte("a"), RangeEnd: []byte("c")}}))
	must(as.RoleGrantPermission(&pb.AuthRoleGrantPermissionRequest{Name: "r",
		Perm: &authpb.Permission{PermType: authpb.WRITE, Key: []byte("w")}}))
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
	return as, toks
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

func TestZZGuardAuthAdmin(t *testing.T) {
	as, toks := zzgSetup(t)
	aa := &AuthAdmin{ag: zzgGetter{as}}
	for _, u := range []string{"root", "u", "v"} {
		zzgIs(t, "requireAuthInfo("+u+")", aa.requireAuthInfo(zzgCtx(toks[u])), nil)
	}
	zzgIs(t, "requireAuthInfo(none)", aa.requireAuthInfo(zzgCtx("")), auth.ErrUserEmpty)
	zzgIs(t, "isPermitted(root)", aa.isPermitted(zzgCtx(toks["root"])), nil)
	zzgIs(t, "isPermitted(u)", aa.isPermitted(zzgCtx(toks["u"])), auth.ErrPermissionDenied)
	zzgIs(t, "isPermitted(none)", aa.isPermitted(zzgCtx("")), auth.ErrUserEmpty)
	// the reason survives togRPCError: one gRPC error per auth error
	for e, g := range map[error]error{
		auth.ErrUserEmpty:        rpctypes.ErrGRPCUserEmpty,
		auth.ErrInvalidAuthToken: rpctypes.ErrGRPCInvalidAuthToken,
		auth.ErrPermissionDenied: rpctypes.ErrGRPCPermissionDenied,
		auth.ErrAuthOldRevision:  rpctypes.ErrGRPCAuthOldRevision,
		auth.ErrUserNotFound:     rpctypes.ErrGRPCUserNotFound,
	} {
		if got := togRPCError(e); got != g {
			t.Errorf("togRPCError(%v) = %v, want %v", e, got, g)
		}
	}
}

func TestZZGuardWatch(t *testing.T) {
	as, toks := zzgSetup(t)
	sws := func(tok string) *serverWatchStream {
		return &serverWatchStream{ag: zzgGetter{as}, gRPCStream: zzgStream{ctx: zzgCtx(tok)}}
	}
	cases := []struct {
		who, key, end string
		want          error
	}{
		{"u", "a", "", nil},                       // a point u may read
		{"u", "a", "c", nil},                      // exactly u's range
		{"u", "b", "c", nil},                      // inside it
		{"root", "z", "\x00", nil},                // root: anything, open-ended included
		{"u", "a", "d", auth.ErrPermissionDenied}, // beyond u's range
		{"u", "w", "", auth.ErrPermissionDenied},  // u may write "w", not read it
		{"v", "a", "", auth.ErrPermissionDenied},  // no role
		{"", "a", "", auth.ErrUserEmpty},          // no token: AuthInfo{} has revision 0
	}
	for _, c := range cases {
		err := sws(toks[c.who]).isWatchPermitted(&pb.WatchCreateRequest{Key: []byte(c.key), RangeEnd: []byte(c.end)})
		zzgIs(t, "watch("+c.who+", "+c.key+", "+c.end+")", err, c.want)
	}
}
