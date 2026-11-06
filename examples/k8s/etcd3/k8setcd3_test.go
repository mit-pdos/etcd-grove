package etcd3

import (
	"os"
	"testing"

	"github.com/anishathalye/porcupine"
	"go.etcd.io/etcd/client/pkg/v3/types"
	"go.etcd.io/etcd/server/v3/etcdserver/api/membership"
	"go.uber.org/zap"
)

// TestMain runs the driver: the store's history is linearizable under Model (Main panics
// otherwise), and the run reaches the check.
func TestMainLinearizable(t *testing.T) {
	os.RemoveAll("k8setcd3.etcd")
	defer os.RemoveAll("k8setcd3.etcd")
	r := Main(4, 60)
	if r != porcupine.Ok {
		t.Fatalf("Main: %v, want Ok", r)
	}
}

// The model's answers on the seeded store: a no-op update of a non-canonical item rewrites it
// (D30g), a no-op update of a canonical one does not.
func TestModelNoopRewrite(t *testing.T) {
	st := mstore{rv: 1}
	st = mstore{items: setItem(st.items, item{key: "a", obj: Obj{Name: "a", Value: "x", ResourceVersion: 2}, canon: false}), rv: 2}
	st1, o1 := mstep(Input{Kind: KUpdate, Key: "a", NoOp: true}, st)
	if st1.rv != 3 || o1.RV != 3 || o1.Value != "x" {
		t.Fatalf("no-op on non-canonical: %+v %+v", st1, o1)
	}
	st2, o2 := mstep(Input{Kind: KUpdate, Key: "a", NoOp: true}, st1)
	if st2.rv != 3 || o2.RV != 3 {
		t.Fatalf("no-op on canonical: %+v %+v", st2, o2)
	}
	_, o3 := mstep(Input{Kind: KDelete, Key: "a", Reject: "x"}, st2)
	if o3.Err != ERejected {
		t.Fatalf("rejected delete: %+v", o3)
	}
	_, o4 := mstep(Input{Kind: KGet, Key: "c"}, st2)
	if o4.Err != ENotFound || o4.ErrKey != "/registry/objs/c" || o4.ErrRV != 3 {
		t.Fatalf("missing get: %+v", o4)
	}
}

// TestMainCluster runs MainCluster once, in a fresh data directory: the store's history over the
// three-member cluster is linearizable under Model (MainCluster panics otherwise), and the run
// reaches the check.
func TestMainCluster(t *testing.T) {
	t.Chdir(t.TempDir())
	r := MainCluster(4, 60)
	if r != porcupine.Ok {
		t.Fatalf("MainCluster: %v, want Ok", r)
	}
}

// TestMemberIDs checks clusterConfig's member ids, as etcd computes them from the names, peer URLs
// and token: their low 16 bits are nonzero and distinct (cluster3's premise on the ids).
func TestMemberIDs(t *testing.T) {
	cfg := clusterConfig()
	urls, err := types.NewURLsMap(cfg.Name1 + "=http://" + cfg.Peer1 + "," + cfg.Name2 + "=http://" +
		cfg.Peer2 + "," + cfg.Name3 + "=http://" + cfg.Peer3)
	if err != nil {
		t.Fatal(err)
	}
	cl, err := membership.NewClusterFromURLsMap(zap.NewNop(), cfg.Token, urls)
	if err != nil {
		t.Fatal(err)
	}
	seen := map[uint64]bool{}
	for _, id := range cl.MemberIDs() {
		low := uint64(id) & 0xffff
		t.Logf("member %x (%s): low 16 bits %#x", uint64(id), cl.Member(id).Name, low)
		if low == 0 || seen[low] {
			t.Fatalf("member %x: low 16 bits %#x zero or repeated", uint64(id), low)
		}
		seen[low] = true
	}
}
