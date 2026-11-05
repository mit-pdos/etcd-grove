package etcd3

import (
	"os"
	"testing"

	"go.uber.org/zap"

	"go.etcd.io/etcd/client/pkg/v3/types"
	clientv3 "go.etcd.io/etcd/client/v3"
	"go.etcd.io/etcd/client/v3/kubernetes"
	"go.etcd.io/etcd/server/v3/config"
	"go.etcd.io/etcd/server/v3/etcdserver"
	"go.etcd.io/etcd/server/v3/etcdserver/api/v3rpc"
	"go.etcd.io/etcd/server/v3/features"
	"net"

	"k8s.io/apimachinery/pkg/runtime/schema"
	"k8s.io/apiserver/pkg/storage/etcd3"
)

// TestCachedNoopPrecondition: GuaranteedUpdate with a cached object, a resource version
// precondition and an update that changes nothing succeeds at the key's current resource version
// when the key was rewritten with the same data since the cached object's (here: the no-op update
// of a non-canonical seed), though the precondition fails on the current object; the Model
// answers "invalid object" (issues/k8s-etcd3-cached-noop-skips-preconditions.md). The test
// passes while the store behaves so.
func TestCachedNoopPrecondition(t *testing.T) {
	os.RemoveAll("k8setcd3n.etcd")
	defer os.RemoveAll("k8setcd3n.etcd")
	lg := zap.NewNop()
	peer := types.URLs{{Scheme: "http", Host: "127.0.0.1:23917"}}
	addr := "127.0.0.1:23887"
	cfg := config.ServerConfig{
		Name: "k8setcd3n", DataDir: "k8setcd3n.etcd",
		InitialPeerURLsMap: types.URLsMap{"k8setcd3n": peer}, PeerURLs: peer,
		ClientURLs:          types.URLs{{Scheme: "http", Host: addr}},
		InitialClusterToken: "k8setcd3n", NewCluster: true, TickMs: 100, ElectionTicks: 10,
		SnapshotCount: etcdserver.DefaultSnapshotCount, SnapshotCatchUpEntries: 1 << 48,
		MaxTxnOps: 128, MaxRequestBytes: 1536 * 1024, Logger: lg,
		ServerFeatureGate: features.NewDefaultServerFeatureGate("k8setcd3n", lg),
	}
	srv, err := etcdserver.NewServer(cfg)
	if err != nil {
		t.Fatal(err)
	}
	srv.Start()
	defer srv.Stop()
	l, err := net.Listen("tcp", addr)
	if err != nil {
		t.Fatal(err)
	}
	go v3rpc.Server(srv, nil, nil).Serve(l)
	kc, err := kubernetes.New(clientv3.Config{Endpoints: []string{addr}, Logger: lg, MaxUnaryRetries: 1})
	if err != nil {
		t.Fatal(err)
	}
	defer kc.Close()
	st, ok := seed(kc.Client)
	if !ok {
		t.Fatal("seed failed")
	}
	s, err := etcd3.New(kc, noCompactor{}, codec{}, newObj, nil, nil, Prefix, ResourcePrefix,
		schema.GroupResource{Resource: "objs"}, identity{}, etcd3.NewDefaultLeaseManagerConfig(),
		decoder{}, versioner{})
	if err != nil {
		t.Fatal(err)
	}
	steps := []Input{
		{Kind: KGet, Key: "a"},
		{Kind: KUpdate, Key: "a", NoOp: true},
		{Kind: KUpdate, Key: "a", NoOp: true, UseCached: true, HasPreRV: true},
	}
	var cached Obj
	for i, in := range steps {
		if i == 2 {
			in.Cached = cached
			in.PreRV = rvString(cached.ResourceVersion)
		}
		next, want := mstep(in, st)
		out := call(s, in)
		t.Logf("op %d %+v: store %+v, model %+v", i, in, out, want)
		if i == 2 && !(out.Err == ENone && out.RV != cached.ResourceVersion && want.Err == EInvalid) {
			t.Fatalf("the store no longer answers the cached no-op past its precondition")
		}
		if i == 0 {
			cached = Obj{Name: out.Name, UID: out.UID, Value: out.Value, ResourceVersion: out.RV}
		}
		st = next
	}
}
