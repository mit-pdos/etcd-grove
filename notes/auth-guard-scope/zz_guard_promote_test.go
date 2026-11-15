// Copy into server/etcdserver/api/etcdhttp at the etcd fork pin 2eaeb872b (notes/auth-guard-scope.md,
// section 4) and run `GOWORK=off go test ./etcdserver/api/etcdhttp/ -run TestZZGuard -v` in server/.
//
// The leader's half of a promotion forwarded by a follower (etcd-io/etcd#20757): the peer handler
// turns the request's Authorization header back into incoming gRPC metadata (peer.go, the fix
// 37531e62f), so the leader's admin guard (checkMembershipOperationPermission's body: AuthInfoFromCtx,
// then IsAdminPermitted) sees root's token and passes. The pre-fix handler passed r.Context() as it
// was: the guard then refuses root with ErrUserEmpty. That refusal meets the guard's converse (no
// token in the context the guard saw); what the converse needs for #20757 is the path's statement
// that the forwarded context carries the caller's token (notes/auth-guard-scope.md, stage G6).
package etcdhttp

import (
	"context"
	"errors"
	"net/http"
	"net/http/httptest"
	"testing"
	"time"

	"go.uber.org/zap/zaptest"
	"golang.org/x/crypto/bcrypt"

	pb "go.etcd.io/etcd/api/v3/etcdserverpb"
	"go.etcd.io/etcd/client/pkg/v3/types"
	"go.etcd.io/etcd/server/v3/auth"
	"go.etcd.io/etcd/server/v3/etcdserver"
	"go.etcd.io/etcd/server/v3/etcdserver/api"
	"go.etcd.io/etcd/server/v3/etcdserver/api/membership"
	betesting "go.etcd.io/etcd/server/v3/storage/backend/testing"
	"go.etcd.io/etcd/server/v3/storage/schema"
)

// zzgLeader is the leader's EtcdServer as far as PromoteMember's guard goes.
type zzgLeader struct {
	etcdserver.Server
	as  auth.AuthStore
	err chan error
}

func (l *zzgLeader) PromoteMember(ctx context.Context, id uint64) ([]*membership.Member, error) {
	ai, err := l.as.AuthInfoFromCtx(ctx)
	if err == nil {
		err = l.as.IsAdminPermitted(ai)
	}
	l.err <- err
	if err != nil {
		return nil, err
	}
	return []*membership.Member{}, nil
}

type zzgCluster struct{ api.Cluster }

func (zzgCluster) ID() types.ID { return 1 }

func zzgRootToken(t *testing.T) (auth.AuthStore, string) {
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
	if _, err := as.UserAdd(&pb.AuthUserAddRequest{Name: "root", Password: "pw"}); err != nil {
		t.Fatal(err)
	}
	if _, err := as.RoleAdd(&pb.AuthRoleAddRequest{Name: "root"}); err != nil {
		t.Fatal(err)
	}
	if _, err := as.UserGrantRole(&pb.AuthUserGrantRoleRequest{User: "root", Role: "root"}); err != nil {
		t.Fatal(err)
	}
	if err := as.AuthEnable(); err != nil {
		t.Fatal(err)
	}
	ctx := context.WithValue(context.WithValue(context.Background(),
		auth.AuthenticateParamIndex{}, uint64(1)), auth.AuthenticateParamSimpleTokenPrefix{}, "pfx")
	resp, err := as.Authenticate(ctx, "root", "")
	if err != nil {
		t.Fatal(err)
	}
	return as, resp.Token
}

func TestZZGuardPromoteLeader(t *testing.T) {
	as, tok := zzgRootToken(t)
	leader := &zzgLeader{as: as, err: make(chan error, 1)}
	h := &peerMemberPromoteHandler{lg: zaptest.NewLogger(t), cluster: zzgCluster{}, server: leader}

	// at the pin: the header becomes the guard's token, root passes
	req := httptest.NewRequest(http.MethodPost, peerMemberPromotePrefix+"5", nil)
	req.Header.Set("Authorization", tok)
	rec := httptest.NewRecorder()
	h.ServeHTTP(rec, req)
	if err := <-leader.err; err != nil || rec.Code != http.StatusOK {
		t.Fatalf("forwarded promotion by root: guard %v, status %d", err, rec.Code)
	}

	// the pre-fix handler: the guard got r.Context() with no metadata
	req = httptest.NewRequest(http.MethodPost, peerMemberPromotePrefix+"5", nil)
	req.Header.Set("Authorization", tok)
	_, _ = leader.PromoteMember(req.Context(), 5)
	if err := <-leader.err; !errors.Is(err, auth.ErrUserEmpty) {
		t.Fatalf("pre-fix: got %v, want ErrUserEmpty", err)
	}
	t.Logf("pre-fix handler: root's forwarded promotion refused with %v", auth.ErrUserEmpty)
}
