// Copy into server/etcdserver/apply at the etcd fork pin 2eaeb872b (notes/auth-guard-scope.md,
// section 4) and run `GOWORK=off go test ./etcdserver/apply/ -run TestZZGuard -v` in server/.
//
// The converse of the apply layer's checks (authApplierV3) on a real auth store with the simple
// token provider and a real lessor: a write or read the principal's roles cover, at the auth
// revision its header carries, passes the RBAC check (Put with PrevKv and a lease, Range,
// DeleteRange, Txn with nested ops in both branches); an admin request from root passes
// needAdminPermission's check. The refusals name the reasons the class allows: a key not covered,
// no principal (revision 0), a header revision older than the store's (an admin change since).
package apply

import (
	"errors"
	"testing"
	"time"

	"go.uber.org/zap/zaptest"
	"golang.org/x/crypto/bcrypt"

	"go.etcd.io/etcd/api/v3/authpb"
	pb "go.etcd.io/etcd/api/v3/etcdserverpb"
	"go.etcd.io/etcd/pkg/v3/traceutil"
	"go.etcd.io/etcd/server/v3/auth"
	"go.etcd.io/etcd/server/v3/etcdserver/api/membership"
	"go.etcd.io/etcd/server/v3/lease"
	betesting "go.etcd.io/etcd/server/v3/storage/backend/testing"
	"go.etcd.io/etcd/server/v3/storage/schema"
)

type zzgInner struct{ applierV3 }

func (zzgInner) Apply(r *InternalRaftRequestWrapper, _ membership.ShouldApplyV3, _ applyFunc) *Result {
	return &Result{}
}
func (zzgInner) Put(*pb.PutRequest) (*pb.PutResponse, *traceutil.Trace, error) {
	return &pb.PutResponse{}, nil, nil
}
func (zzgInner) Range(*pb.RangeRequest) (*pb.RangeResponse, *traceutil.Trace, error) {
	return &pb.RangeResponse{}, nil, nil
}
func (zzgInner) DeleteRange(*pb.DeleteRangeRequest) (*pb.DeleteRangeResponse, *traceutil.Trace, error) {
	return &pb.DeleteRangeResponse{}, nil, nil
}
func (zzgInner) Txn(*pb.TxnRequest, bool) (*pb.TxnResponse, *traceutil.Trace, error) {
	return &pb.TxnResponse{}, nil, nil
}

func zzgIs(t *testing.T, what string, err, want error) {
	t.Helper()
	if !errors.Is(err, want) && !(err == nil && want == nil) {
		t.Errorf("%s: got %v, want %v", what, err, want)
	}
}

func TestZZGuardApplyRBAC(t *testing.T) {
	lg := zaptest.NewLogger(t)
	be, _ := betesting.NewDefaultTmpBackend(t)
	defer betesting.Close(t, be)
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
	for _, u := range []string{"root", "u"} {
		must(as.UserAdd(&pb.AuthUserAddRequest{Name: u, Password: "pw"}))
	}
	must(as.RoleAdd(&pb.AuthRoleAddRequest{Name: "root"}))
	must(as.RoleAdd(&pb.AuthRoleAddRequest{Name: "r"}))
	must(as.RoleGrantPermission(&pb.AuthRoleGrantPermissionRequest{Name: "r",
		Perm: &authpb.Permission{PermType: authpb.READWRITE, Key: []byte("k/"), RangeEnd: []byte("k0")}}))
	must(as.RoleGrantPermission(&pb.AuthRoleGrantPermissionRequest{Name: "r",
		Perm: &authpb.Permission{PermType: authpb.READ, Key: []byte("ro")}}))
	must(as.UserGrantRole(&pb.AuthUserGrantRoleRequest{User: "root", Role: "root"}))
	must(as.UserGrantRole(&pb.AuthUserGrantRoleRequest{User: "u", Role: "r"}))
	if err := as.AuthEnable(); err != nil {
		t.Fatal(err)
	}
	le := lease.NewLessor(lg, be, nil, lease.LessorConfig{MinLeaseTTL: 10})
	defer le.Stop()
	l, err := le.Grant(1, 60)
	if err != nil {
		t.Fatal(err)
	}
	if err := le.Attach(l.ID, []lease.LeaseItem{{Key: "k/held"}}); err != nil {
		t.Fatal(err)
	}

	rev := as.Revision()
	aa := newAuthApplierV3(as, zzgInner{}, le)
	aa.authInfo = auth.AuthInfo{Username: "u", Revision: rev}

	// served: everything u's roles cover
	_, _, err = aa.Put(&pb.PutRequest{Key: []byte("k/x"), PrevKv: true, Lease: int64(l.ID)})
	zzgIs(t, "Put(k/x, prevKv, lease)", err, nil)
	_, _, err = aa.Range(&pb.RangeRequest{Key: []byte("k/"), RangeEnd: []byte("k0")})
	zzgIs(t, "Range([k/, k0))", err, nil)
	_, _, err = aa.Range(&pb.RangeRequest{Key: []byte("ro")})
	zzgIs(t, "Range(ro)", err, nil)
	_, _, err = aa.DeleteRange(&pb.DeleteRangeRequest{Key: []byte("k/a"), RangeEnd: []byte("k/b"), PrevKv: true})
	zzgIs(t, "DeleteRange([k/a, k/b), prevKv)", err, nil)
	txn := &pb.TxnRequest{
		Compare: []*pb.Compare{{Key: []byte("ro"), Target: pb.Compare_VERSION}},
		Success: []*pb.RequestOp{{Request: &pb.RequestOp_RequestPut{RequestPut: &pb.PutRequest{Key: []byte("k/y")}}}},
		Failure: []*pb.RequestOp{{Request: &pb.RequestOp_RequestTxn{RequestTxn: &pb.TxnRequest{
			Success: []*pb.RequestOp{{Request: &pb.RequestOp_RequestRange{RequestRange: &pb.RangeRequest{Key: []byte("ro")}}}},
		}}}},
	}
	_, _, err = aa.Txn(txn, false)
	zzgIs(t, "Txn(both branches covered)", err, nil)

	// refused, with a reason the class allows
	_, _, err = aa.Put(&pb.PutRequest{Key: []byte("ro")})
	zzgIs(t, "Put(ro): read-only key", err, auth.ErrPermissionDenied)
	_, _, err = aa.Range(&pb.RangeRequest{Key: []byte("k/"), RangeEnd: []byte("k1")})
	zzgIs(t, "Range([k/, k1)): beyond the grant", err, auth.ErrPermissionDenied)
	aa.authInfo = auth.AuthInfo{Username: "u", Revision: rev - 1}
	_, _, err = aa.Range(&pb.RangeRequest{Key: []byte("ro")})
	zzgIs(t, "Range(ro) at an older revision", err, auth.ErrAuthOldRevision)
	aa.authInfo = auth.AuthInfo{}
	_, _, err = aa.Range(&pb.RangeRequest{Key: []byte("ro")})
	zzgIs(t, "Range(ro) with no principal", err, auth.ErrUserEmpty)

	// admin at apply: root's header passes needAdminPermission's check, u's is refused
	req := func(user string) *InternalRaftRequestWrapper {
		return &InternalRaftRequestWrapper{InternalRaftRequest: &pb.InternalRaftRequest{
			Header:      &pb.RequestHeader{Username: user, AuthRevision: as.Revision()},
			AuthUserAdd: &pb.AuthUserAddRequest{Name: "new", Password: "pw"},
		}}
	}
	zzgIs(t, "Apply(UserAdd, root)", aa.Apply(req("root"), membership.ApplyBoth, nil).Err, nil)
	zzgIs(t, "Apply(UserAdd, u)", aa.Apply(req("u"), membership.ApplyBoth, nil).Err, auth.ErrPermissionDenied)
}
