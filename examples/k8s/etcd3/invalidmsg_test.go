package etcd3

import (
	"errors"
	"net"
	"os"
	"strings"
	"testing"

	"go.uber.org/zap"

	"go.etcd.io/etcd/client/pkg/v3/types"
	clientv3 "go.etcd.io/etcd/client/v3"
	"go.etcd.io/etcd/client/v3/kubernetes"
	"go.etcd.io/etcd/server/v3/config"
	"go.etcd.io/etcd/server/v3/etcdserver"
	"go.etcd.io/etcd/server/v3/etcdserver/api/v3rpc"
	"go.etcd.io/etcd/server/v3/features"

	"k8s.io/apimachinery/pkg/runtime/schema"
	"k8s.io/apiserver/pkg/storage/etcd3"
)

// TestInvalidMsg (k8s 7g, the step-4 STOP's option (C)): a failed precondition's output carries
// Preconditions.Check's message (ErrMsg, from the store's NewInvalidObjError), in its UID form and
// its resource-version form, for an update and a delete; the message names the stored object's UID
// or resource version; and the Model predicts the whole output (outEqual), message included.
func TestInvalidMsg(t *testing.T) {
	os.RemoveAll("k8setcd3m.etcd")
	defer os.RemoveAll("k8setcd3m.etcd")
	lg := zap.NewNop()
	peer := types.URLs{{Scheme: "http", Host: "127.0.0.1:23927"}}
	addr := "127.0.0.1:23928"
	cfg := config.ServerConfig{
		Name: "k8setcd3m", DataDir: "k8setcd3m.etcd",
		InitialPeerURLsMap: types.URLsMap{"k8setcd3m": peer}, PeerURLs: peer,
		ClientURLs:          types.URLs{{Scheme: "http", Host: addr}},
		InitialClusterToken: "k8setcd3m", NewCluster: true, TickMs: 100, ElectionTicks: 10,
		SnapshotCount: etcdserver.DefaultSnapshotCount, SnapshotCatchUpEntries: 1 << 48,
		MaxTxnOps: 128, MaxRequestBytes: 1536 * 1024, Logger: lg,
		ServerFeatureGate: features.NewDefaultServerFeatureGate("k8setcd3m", lg),
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
	st, _, ok := seed(kc.Client)
	if !ok {
		t.Fatal("seed failed")
	}
	s, err := etcd3.New(kc, noCompactor{}, codec{}, newObj, nil, nil, Prefix, ResourcePrefix,
		schema.GroupResource{Resource: "objs"}, identity{}, etcd3.NewDefaultLeaseManagerConfig(),
		decoder{}, versioner{})
	if err != nil {
		t.Fatal(err)
	}
	// an object with a UID (the seeds have none)
	key := "ns-1/msg"
	mk := Input{Kind: KCreate, Key: key, UID: "uid-msg", Val: "v"}
	next, want := mstep(mk, st)
	if out := call(s, mk); out.Err != ENone || !outEqual(out, want) {
		t.Fatalf("create: store %+v, model %+v", out, want)
	}
	st = next
	cur, ok := lookup(st.items, key)
	if !ok || cur.obj.UID != "uid-msg" {
		t.Fatalf("the model has no %s with its UID", key)
	}
	steps := []struct {
		in   Input
		want string // the part of the message naming the stored object
	}{
		{Input{Kind: KUpdate, Key: key, NoOp: true, HasPreUID: true, PreUID: "no-such-uid"},
			"UID in object meta: " + cur.obj.UID},
		{Input{Kind: KUpdate, Key: key, NoOp: true, HasPreRV: true, PreRV: "1"},
			"ResourceVersion in object meta: " + rvString(cur.obj.ResourceVersion)},
		{Input{Kind: KDelete, Key: key, HasPreUID: true, PreUID: "no-such-uid"},
			"UID in object meta: " + cur.obj.UID},
		{Input{Kind: KDelete, Key: key, HasPreRV: true, PreRV: "1"},
			"ResourceVersion in object meta: " + rvString(cur.obj.ResourceVersion)},
	}
	for i, sp := range steps {
		next, want := mstep(sp.in, st)
		out := call(s, sp.in)
		t.Logf("op %d %+v: store %+v, model %+v", i, sp.in, out, want)
		if out.Err != EInvalid {
			t.Fatalf("op %d: store answered %+v, want EInvalid", i, out)
		}
		chk := preconditions(sp.in).Check(out.ErrKey, &cur.obj)
		if chk == nil || out.ErrMsg != errors.Unwrap(chk).Error() {
			t.Fatalf("op %d: ErrMsg %q, Check's message %v", i, out.ErrMsg, chk)
		}
		if !strings.HasSuffix(out.ErrMsg, sp.want) {
			t.Fatalf("op %d: ErrMsg %q does not end in %q", i, out.ErrMsg, sp.want)
		}
		if out.ErrMsg != preMsg(sp.in, cur.obj) || !outEqual(out, want) {
			t.Fatalf("op %d: the Model's output %+v, the store's %+v", i, want, out)
		}
		st = next
	}
}
