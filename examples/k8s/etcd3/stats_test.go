package etcd3

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
// storage errors, rejections, the rewrite of a non-canonical item, and lists of every mode,
// scope and selector (with a too-large resource version, a stale answer at a past revision, a
// continue token and a remaining count among them); the model's history has one store per
// revision throughout.
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
	st0, h0, ok := seed(kc.Client)
	if !ok || !noStreaming() {
		t.Fatal("seed or the gate switch failed")
	}
	c := mcfg{st: st0, hist: histOf(h0)}
	s, err := etcd3.New(kc, noCompactor{}, codec{}, newObj, nil, nil, Prefix, ResourcePrefix,
		schema.GroupResource{Resource: "objs"}, identity{}, etcd3.NewDefaultLeaseManagerConfig(),
		decoder{}, versioner{})
	if err != nil {
		t.Fatal(err)
	}
	counts := map[string]int{}
	tbl := newCache()
	kinds := []string{"create", "delete", "update", "get", "list"}
	errs := []string{"ok", "notfound", "exists", "rejected", "other", "invalid", "toolarge"}
	for i := 0; i < 3000; i++ {
		in := Gen(tbl, i%3)
		before := c.st
		out := call(s, in)
		if out.Err == ENone && out.Name != "" {
			tbl.put(in.Client, objOf(out))
		}
		if out.Err == EOther {
			t.Fatalf("op %d %+v: unexpected error", i, in)
		}
		next, want := seqStep(in, c)
		if !outEqual(out, want) {
			t.Fatalf("op %d %+v: got %+v, model %+v", i, in, out, want)
		}
		if histLen(next.hist) != next.st.rv {
			t.Fatalf("op %d: %d stores in the history at revision %d", i, histLen(next.hist), next.st.rv)
		}
		c = next
		counts[kinds[in.Kind]+"/"+errs[out.Err]]++
		if in.UseCached {
			counts[kinds[in.Kind]+"/cached/"+errs[out.Err]]++
		}
		if in.Kind == KList && out.Err == ENone {
			req, _ := parseRV(in.MinRV)
			mode := "latest"
			if pastRead(in, req) {
				mode = "past"
				if req < c.st.rv && !listEqualAt(in, c, req, c.st.rv) {
					counts["list/past/stale"]++ // the answer differs from the current store's
				}
			}
			counts["list/"+mode]++
			if in.Recursive {
				counts["list/recursive"]++
			} else {
				counts["list/nonrecursive"]++
			}
			if out.Continue != "" {
				counts["list/continue"]++
			}
			if out.HasRemaining {
				counts["list/remaining"]++
			}
			if len(out.Items) == 0 {
				counts["list/empty"]++
			}
			counts[[]string{"list/field/everything", "list/field/name", "list/field/ns",
				"list/field/node", "list/field/emptynode", "list/field/combined"}[in.Field]]++
			if in.SelApp != "" {
				counts["list/label/app"]++
			}
			counts[[]string{"list/match/legacy", "list/match/notolderthan", "list/match/exact"}[in.Match]]++
		}
		if in.Kind == KUpdate && in.IgnoreNotFound && out.Err == ENone {
			if _, ok := lookup(before.items, in.Key); !ok {
				counts["update/ignorenotfound-create"]++
			}
		}
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
		"get/notfound", "update/noop-skip", "delete/invalid", "update/invalid", "get/toolarge",
		"delete/cached/ok", "update/cached/ok", "update/ignorenotfound-create",
		"list/ok", "list/toolarge", "list/latest", "list/past", "list/past/stale", "list/recursive",
		"list/nonrecursive", "list/continue", "list/remaining", "list/empty",
		"list/field/everything", "list/field/name", "list/field/ns", "list/field/node",
		"list/field/emptynode", "list/field/combined", "list/label/app", "list/match/legacy",
		"list/match/notolderthan", "list/match/exact"} {
		if counts[k] == 0 {
			t.Errorf("no %s outcome", k)
		}
	}
}

// seqStep is the model's step on one configuration for a call that returned (no failed write):
// its next configuration and its answer.
func seqStep(in Input, c mcfg) (mcfg, Output) {
	if in.Kind == KList {
		return c, mlist(in, c)
	}
	st, o := mstep(in, c.st)
	return advance(c, st, c.pend), o
}

// listEqualAt says whether a List's items at revision r are its items at revision r2 (as latest
// reads of the stores at r and r2).
func listEqualAt(in Input, c mcfg, r uint64, r2 uint64) bool {
	in.MinRV, in.Match = "", MLegacy
	a := mlist(in, mcfg{st: histAt(c.hist, r)})
	b := mlist(in, mcfg{st: histAt(c.hist, r2)})
	if len(a.Items) != len(b.Items) {
		return false
	}
	for i := range a.Items {
		if a.Items[i] != b.Items[i] {
			return false
		}
	}
	return true
}
