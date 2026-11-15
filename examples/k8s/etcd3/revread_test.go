package etcd3

import (
	"context"
	"errors"
	"net"
	"os"
	"testing"

	"go.uber.org/zap"

	"go.etcd.io/etcd/api/v3/v3rpc/rpctypes"
	"go.etcd.io/etcd/client/pkg/v3/types"
	clientv3 "go.etcd.io/etcd/client/v3"
	"go.etcd.io/etcd/client/v3/kubernetes"
	"go.etcd.io/etcd/server/v3/config"
	"go.etcd.io/etcd/server/v3/etcdserver"
	"go.etcd.io/etcd/server/v3/etcdserver/api/v3rpc"
	"go.etcd.io/etcd/server/v3/features"
)

// TestReadAtRevision (k8s etcd3 stage 7c, 7c-0): kubernetes.Client.Get at a revision, against an
// in-process member, as notes/k8s-etcd3-plan.md "7c: Scope" states it:
//   - a past revision returns the key as it was then, at the response's (current) revision;
//   - a future revision fails with an error that errors.Is rpctypes.ErrFutureRev (listReadError's
//     test) and whose description is "etcdserver: mvcc: required revision is a future revision";
//   - a compacted revision fails with an error == rpctypes.ErrCompacted (interpretListError's
//     test) whose description is "etcdserver: mvcc: required revision has been compacted";
//   - the descriptions are the server-side ErrGRPC* ones (the trust statements' claim).
//
// It also checks List's Count with Continue set (the documentation mismatch the Scope found).
func TestReadAtRevision(t *testing.T) {
	os.RemoveAll("k8setcd3r.etcd")
	defer os.RemoveAll("k8setcd3r.etcd")
	lg := zap.NewNop()
	peer := types.URLs{{Scheme: "http", Host: "127.0.0.1:23918"}}
	addr := "127.0.0.1:23888"
	cfg := config.ServerConfig{
		Name: "k8setcd3r", DataDir: "k8setcd3r.etcd",
		InitialPeerURLsMap: types.URLsMap{"k8setcd3r": peer}, PeerURLs: peer,
		ClientURLs:          types.URLs{{Scheme: "http", Host: addr}},
		InitialClusterToken: "k8setcd3r", NewCluster: true, TickMs: 100, ElectionTicks: 10,
		SnapshotCount: etcdserver.DefaultSnapshotCount, SnapshotCatchUpEntries: 1 << 48,
		MaxTxnOps: 128, MaxRequestBytes: 1536 * 1024, Logger: lg,
		ServerFeatureGate: features.NewDefaultServerFeatureGate("k8setcd3r", lg),
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
	ctx := context.Background()

	if got, want := rpctypes.ErrorDesc(rpctypes.ErrGRPCFutureRev), "etcdserver: mvcc: required revision is a future revision"; got != want {
		t.Fatalf("ErrGRPCFutureRev's description %q, want %q", got, want)
	}
	if got, want := rpctypes.ErrorDesc(rpctypes.ErrGRPCCompacted), "etcdserver: mvcc: required revision has been compacted"; got != want {
		t.Fatalf("ErrGRPCCompacted's description %q, want %q", got, want)
	}

	p1, err := kc.Put(ctx, "k", "v1")
	if err != nil {
		t.Fatal(err)
	}
	r1 := p1.Header.Revision
	p2, err := kc.Put(ctx, "k", "v2")
	if err != nil {
		t.Fatal(err)
	}
	r2 := p2.Header.Revision

	// a past revision: the key as it was then, the response's revision the current one
	g, err := kc.Kubernetes.Get(ctx, "k", kubernetes.GetOptions{Revision: r1})
	if err != nil {
		t.Fatal(err)
	}
	if g.KV == nil || string(g.KV.Value) != "v1" || g.KV.ModRevision != r1 || g.Revision != r2 {
		t.Fatalf("Get at %d: %v at revision %d", r1, g.KV, g.Revision)
	}
	// revision 0: the latest
	g, err = kc.Kubernetes.Get(ctx, "k", kubernetes.GetOptions{})
	if err != nil || g.KV == nil || string(g.KV.Value) != "v2" {
		t.Fatalf("Get latest: %v %v", g.KV, err)
	}
	// a List at a past revision (k8s 7e-1, Client.List.spec): the prefix's key-values then, its
	// count then, the response's revision the current one
	lp, err := kc.Kubernetes.List(ctx, "k", kubernetes.ListOptions{Revision: r1})
	if err != nil || len(lp.Kvs) != 1 || string(lp.Kvs[0].Value) != "v1" || lp.Count != 1 || lp.Revision != r2 {
		t.Fatalf("List at %d: %v (count %d) at revision %d, %v", r1, lp.Kvs, lp.Count, lp.Revision, err)
	}

	// a future revision
	_, err = kc.Kubernetes.Get(ctx, "k", kubernetes.GetOptions{Revision: r2 + 10})
	if err == nil || !errors.Is(err, rpctypes.ErrFutureRev) {
		t.Fatalf("Get at a future revision: %v", err)
	}
	if rpctypes.ErrorDesc(err) != rpctypes.ErrorDesc(rpctypes.ErrGRPCFutureRev) {
		t.Fatalf("future revision's description %q", rpctypes.ErrorDesc(err))
	}
	_, err = kc.Kubernetes.List(ctx, "k", kubernetes.ListOptions{Revision: r2 + 10})
	if err == nil || !errors.Is(err, rpctypes.ErrFutureRev) {
		t.Fatalf("List at a future revision: %v", err)
	}

	// a compacted revision
	if _, err := kc.Compact(ctx, r2); err != nil {
		t.Fatal(err)
	}
	_, err = kc.Kubernetes.Get(ctx, "k", kubernetes.GetOptions{Revision: r1})
	if err != rpctypes.ErrCompacted {
		t.Fatalf("Get at a compacted revision: %v", err)
	}
	if rpctypes.ErrorDesc(err) != rpctypes.ErrorDesc(rpctypes.ErrGRPCCompacted) {
		t.Fatalf("compacted revision's description %q", rpctypes.ErrorDesc(err))
	}
	_, err = kc.Kubernetes.List(ctx, "k", kubernetes.ListOptions{Revision: r1})
	if err != rpctypes.ErrCompacted {
		t.Fatalf("List at a compacted revision: %v", err)
	}
	// the compaction revision itself is still readable
	g, err = kc.Kubernetes.Get(ctx, "k", kubernetes.GetOptions{Revision: r2})
	if err != nil || g.KV == nil || string(g.KV.Value) != "v2" {
		t.Fatalf("Get at the compaction revision: %v %v", g.KV, err)
	}

	// List's Count with Continue: the keys from Continue to the prefix's end, not the prefix's
	for _, k := range []string{"p/a", "p/b", "p/c"} {
		if _, err := kc.Put(ctx, k, "x"); err != nil {
			t.Fatal(err)
		}
	}
	lr, err := kc.Kubernetes.List(ctx, "p/", kubernetes.ListOptions{Limit: 1, Continue: "p/b"})
	if err != nil {
		t.Fatal(err)
	}
	if len(lr.Kvs) != 1 || string(lr.Kvs[0].Key) != "p/b" || lr.Count != 2 {
		t.Fatalf("List from p/b: %d kvs, count %d", len(lr.Kvs), lr.Count)
	}
}
