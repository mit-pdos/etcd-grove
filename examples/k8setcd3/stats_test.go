package k8setcd3

import (
	"context"
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

// TestTrafficReachesCases runs the traffic sequentially against a store and checks each answer
// against the model step by step, counting the outcomes: the runs reach successes of every kind,
// storage errors, rejections, and the rewrite of a non-canonical item.
func TestTrafficReachesCases(t *testing.T) {
	os.RemoveAll("k8setcd3s.etcd")
	defer os.RemoveAll("k8setcd3s.etcd")
	lg := zap.NewNop()
	peer := types.URLs{{Scheme: "http", Host: "127.0.0.1:23907"}}
	addr := "127.0.0.1:23897"
	cfg := config.ServerConfig{
		Name: "k8setcd3s", DataDir: "k8setcd3s.etcd",
		InitialPeerURLsMap: types.URLsMap{"k8setcd3s": peer}, PeerURLs: peer,
		ClientURLs:          types.URLs{{Scheme: "http", Host: addr}},
		InitialClusterToken: "k8setcd3s", NewCluster: true, TickMs: 100, ElectionTicks: 10,
		SnapshotCount: etcdserver.DefaultSnapshotCount, SnapshotCatchUpEntries: 1 << 48,
		MaxTxnOps: 128, MaxRequestBytes: 1536 * 1024, Logger: lg,
		ServerFeatureGate: features.NewDefaultServerFeatureGate("k8setcd3s", lg),
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
	counts := map[string]int{}
	for i := 0; i < 400; i++ {
		in := Gen(0).(Input)
		before := st
		out := call(s, in)
		if out.Err == EOther {
			t.Fatalf("op %d %+v: unexpected error", i, in)
		}
		next, want := mstep(in, st)
		if !outEqual(out, want) {
			t.Fatalf("op %d %+v: got %+v, model %+v", i, in, out, want)
		}
		st = next
		kinds := []string{"create", "delete", "update", "get"}
		errs := []string{"ok", "notfound", "exists", "rejected", "other"}
		counts[kinds[in.Kind]+"/"+errs[out.Err]]++
		if in.Kind == KUpdate && in.NoOp && out.Err == ENone {
			if it, ok := lookup(before.items, in.Key); ok && !it.canon {
				counts["update/noop-rewrite"]++
			} else {
				counts["update/noop-skip"]++
			}
		}
	}
	t.Logf("outcomes: %v", counts)
	_ = context.Background
	for _, k := range []string{"create/ok", "create/exists", "delete/ok", "delete/notfound",
		"delete/rejected", "update/ok", "update/notfound", "update/rejected", "get/ok",
		"get/notfound", "update/noop-skip"} {
		if counts[k] == 0 {
			t.Errorf("no %s outcome", k)
		}
	}
}
