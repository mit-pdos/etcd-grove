package apply

import (
	"regexp"
	"testing"

	"github.com/stretchr/testify/require"
	"go.uber.org/zap/zaptest"

	"go.etcd.io/etcd/api/v3/authpb"
	pb "go.etcd.io/etcd/api/v3/etcdserverpb"
	"go.etcd.io/etcd/server/v3/auth"
	"go.etcd.io/etcd/server/v3/lease"
	betesting "go.etcd.io/etcd/server/v3/storage/backend/testing"
	"go.etcd.io/etcd/server/v3/storage/schema"
)

// Records of role r that two members hold after applying the same RoleGrantPermission entries,
// one built with go1.17.13 (etcd v3.5.7's toolchain), one with go1.19.9 (v3.5.9's): the output
// of sortcmp/main.go and sorttyped (see the .md file). The records are written to the members'
// backends directly; this test does not run two toolchains.
var permRe = regexp.MustCompile(`\[([^,\]]*),([^)]*)\)(RW|R)?`)

// parseRecord reads "[k,e)[k,e)..." (READWRITE) or "[k,e)R[k,e)RW..." (typed).
func parseRecord(s string) []*authpb.Permission {
	var ps []*authpb.Permission
	for _, m := range permRe.FindAllStringSubmatch(s, -1) {
		ty := authpb.READWRITE
		if m[3] == "R" {
			ty = authpb.READ
		}
		ps = append(ps, &authpb.Permission{PermType: ty, Key: []byte(m[1]), RangeEnd: []byte(m[2])})
	}
	return ps
}

// member: an auth store (auth enabled, user u with role r) whose backend holds r's record,
// reopened as on a restart, so that the range-permission cache is built from the record.
func member(t *testing.T, record string) auth.AuthStore {
	be, _ := betesting.NewDefaultTmpBackend(t)
	t.Cleanup(func() { betesting.Close(t, be) })
	as := setupAuth(t, be)
	_, err := as.RoleAdd(&pb.AuthRoleAddRequest{Name: "r"})
	require.NoError(t, err)
	_, err = as.UserAdd(&pb.AuthUserAddRequest{Name: "u", Password: "u"})
	require.NoError(t, err)
	_, err = as.UserGrantRole(&pb.AuthUserGrantRoleRequest{User: "u", Role: "r"})
	require.NoError(t, err)
	lg := zaptest.NewLogger(t)
	ab := schema.NewAuthBackend(lg, be)
	tx := ab.BatchTx()
	tx.Lock()
	tx.UnsafePutRole(&authpb.Role{Name: []byte("r"), KeyPermission: parseRecord(record)})
	tx.Unlock()
	be.ForceCommit()
	as.Close()
	tp, err := auth.NewTokenProvider(lg, "simple", func(uint64) <-chan struct{} {
		ch := make(chan struct{}, 1)
		ch <- struct{}{}
		return ch
	}, 300e9)
	require.NoError(t, err)
	return auth.NewAuthStore(lg, ab, tp, 4)
}

func verdicts(t *testing.T, recA, recB string, txn *pb.TxnRequest) (error, error) {
	a, b := member(t, recA), member(t, recB)
	errA := CheckTxnAuth(a, &auth.AuthInfo{Username: "u", Revision: a.Revision()}, &lease.FakeLessor{}, txn)
	errB := CheckTxnAuth(b, &auth.AuthInfo{Username: "u", Revision: b.Revision()}, &lease.FakeLessor{}, txn)
	return errA, errB
}

// The same permission set in the two orders (the fork's RoleGrantPermission, sortcmp seq 4):
// a write Txn reading an inverted range is refused on one member and applied on the other.
func TestPermOrderInvertedRangeTxn(t *testing.T) {
	go117 := "[a,c)[b,f)[b,g)[b,d)[b,e)[c,e)[c,d)[d,i)[d,h)[d,f)[e,i)[e,h)[f,h)[f,i)[f,g)"
	go119 := "[a,c)[b,d)[b,g)[b,e)[b,f)[c,e)[c,d)[d,h)[d,i)[d,f)[e,i)[e,h)[f,h)[f,i)[f,g)"
	txn := &pb.TxnRequest{Success: []*pb.RequestOp{
		{Request: &pb.RequestOp_RequestRange{RequestRange: &pb.RangeRequest{Key: []byte("d"), RangeEnd: []byte("a")}}},
		{Request: &pb.RequestOp_RequestPut{RequestPut: &pb.PutRequest{Key: []byte("a"), Value: []byte("v")}}},
	}}
	errA, errB := verdicts(t, go117, go119, txn)
	t.Logf("Txn{range [d,a); put a}: go1.17 member %v, go1.19 member %v", errA, errB)
	if (errA == nil) != (errB == nil) {
		t.Errorf("the members disagree on the same committed Txn")
	}
}

// Upstream's RoleGrantPermission (sorttyped seq 0): the two members' records hold different
// permission sets, and a plain put is refused on one member and applied on the other.
func TestPermOrderPutUpstream(t *testing.T) {
	go117 := "[a,c)RW[a,d)RW[a,d)R[a,d)R[b,d)R[b,e)R[b,c)R[b,e)R[c,d)R[c,f)R[d,e)R[d,f)R[e,f)RW[f,g)RW[f,h)RW[f,i)RW[f,i)R"
	go119 := "[a,c)RW[a,c)R[a,d)R[b,e)R[b,c)R[b,d)R[b,d)R[c,d)R[c,f)R[d,e)R[d,f)R[e,f)RW[f,g)RW[f,h)RW[f,i)RW[f,i)R"
	txn := &pb.TxnRequest{Success: []*pb.RequestOp{
		{Request: &pb.RequestOp_RequestPut{RequestPut: &pb.PutRequest{Key: []byte("c"), Value: []byte("v")}}},
	}}
	errA, errB := verdicts(t, go117, go119, txn)
	t.Logf("Txn{put c}: go1.17 member %v, go1.19 member %v", errA, errB)
	if (errA == nil) != (errB == nil) {
		t.Errorf("the members disagree on the same committed put")
	}
}
