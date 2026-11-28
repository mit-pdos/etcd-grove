package etcd3

// Stage 7g (notes/k8s-7g-scope.md §8): Kubernetes' own checker (realCheck, over the copy in
// ./correctness) on the driver's real histories, and the facts its departures rest on.

import (
	"os"
	"testing"
	"time"

	"github.com/anishathalye/porcupine"
	"go.uber.org/zap"

	clientv3 "go.etcd.io/etcd/client/v3"
	"go.etcd.io/etcd/client/v3/kubernetes"

	"k8s.io/apimachinery/pkg/api/meta"
	metav1 "k8s.io/apimachinery/pkg/apis/meta/v1"
	"k8s.io/apimachinery/pkg/watch"
	"k8s.io/apiserver/pkg/storage"

	"github.com/mit-pdos/etcd-grove/examples/k8s/etcd3/correctness"
	"github.com/mit-pdos/etcd-grove/examples/lib/cluster3"
	"github.com/mit-pdos/etcd-grove/examples/lib/etcdstart"
	"github.com/mit-pdos/etcd-grove/examples/lib/lintest"
	"github.com/mit-pdos/etcd-grove/examples/lib/walarea"
)

// checkRealLogged is Check (the same cache, RunLin2 call, failureFree and realCheck), logging the
// driver's verdict, whether the history is failure-free, the real checker's verdict and the
// counts. It fails the test if the driver's verdict is not Ok, or if a failure-free history is
// not Ok under the real checker.
func checkRealLogged(t *testing.T, s storage.Interface, st0 mstore, h0 []mstore, clients, ops, watchers, wops int) {
	tbl := newWCache(clients, int64(clients)*int64(ops), st0.rv)
	apply := func(input any) any { return Apply(s, tbl, input) }
	gen := func(id int) any { return Gen(tbl, id) }
	r, lops := lintest.RunLin2(Model(st0, h0), apply, gen, lintest.CounterClock(), clients, ops, watchers, wops, 0)
	var unary, failed, ws, wfailed, events int
	for _, op := range lops {
		in, out := op.Input.(Input), op.Output.(Output)
		if in.Kind == KWatch {
			if !in.Skip {
				ws++
				if out.WFailed {
					wfailed++
				}
				events += len(out.Raw.Events)
			}
			continue
		}
		unary++
		if out.Err == EOther {
			failed++
		}
	}
	t.Logf("floor %d; driver's check %v; unary %d (failed %d), watches %d (failed %d, %d events)",
		st0.rv, r, unary, failed, ws, wfailed, events)
	if r != porcupine.Ok {
		t.Fatalf("driver's check: %v", r)
	}
	if !failureFree(lops) {
		t.Logf("not failure-free: the real checker does not run")
		return
	}
	start := time.Now()
	rr := realCheck(st0, lops, 0)
	t.Logf("real checker: %v in %v", rr, time.Since(start))
	if rr != porcupine.Ok {
		t.Fatalf("real checker: %v", rr)
	}
}

// TestRealChecker: one member (Main's setup, on ports of its own), 8 unary clients of 300
// operations and 16 watchers of 8 watches, in a process of its own (inChild). Member k8s7g's WAL
// area and data directory (fixed paths, under etcdstart.WALBase and DataBase) are made empty before
// the run and removed after it, so that a run never starts from a previous run's WAL.
func TestRealChecker(t *testing.T) {
	inChild(t, "TestRealChecker", "", func(t *testing.T) {
		walarea.Reset(t, "k8s7g")
		t.Cleanup(func() {
			os.RemoveAll(walarea.Area("k8s7g"))
			os.RemoveAll(walarea.DataDir("k8s7g"))
		})
		lg := zap.NewNop()
		cl := "127.0.0.1:23991"
		srv, err := etcdstart.StartServer("k8s7g", "127.0.0.1:23990", cl, lg)
		if err != nil {
			t.Fatal(err)
		}
		if err := etcdstart.Serve(srv, cl); err != nil {
			t.Fatal(err)
		}
		kc, err := kubernetes.New(clientv3.Config{Endpoints: []string{cl}, Logger: lg, MaxUnaryRetries: 1})
		if err != nil {
			t.Fatal(err)
		}
		s, st0, h0, ok := newStore(kc)
		if !ok {
			t.Fatal("newStore")
		}
		checkRealLogged(t, s, st0, h0, 8, 300, 16, 8)
	})
}

// TestRealCheckerPartition: testK members under each schedule (K8SETCD3_SCHED names one; all by
// default), 4 unary clients of 120 operations and 8 watchers of 12 watches, each in a process of
// its own. Runs with failed calls are not checked by the real checker (design A').
func TestRealCheckerPartition(t *testing.T) {
	only := os.Getenv("K8SETCD3_SCHED")
	k := testK(t)
	for name, sched := range partitionSchedules(int(k)) {
		if only != "" && name != only {
			continue
		}
		t.Run(name, func(t *testing.T) {
			inChild(t, "TestRealCheckerPartition", name, func(t *testing.T) {
				srvs, brs, kc, ok := startCluster(k, zap.NewNop())
				if !ok {
					t.Fatal("startCluster")
				}
				s, st0, h0, ok := newStore(kc)
				if !ok {
					t.Fatal("newStore")
				}
				go cluster3.Partitioner(srvs, brs, sched)
				checkRealLogged(t, s, st0, h0, 4, 120, 8, 12)
			})
		})
	}
}

// TestD30gRealModel: a seeded non-canonical key's no-op update, which the store rewrites at a new
// resource version (the driver's model says the same), is accepted by the patched Model of
// initialModel and rejected once the key's NeedsRewrite entry is gone (upstream's Model; the
// nonissue k8s-correctness-model-noop-rewrite).
func TestD30gRealModel(t *testing.T) {
	st0 := mstore{items: []item{{key: "ns-1/pod-1", obj: Obj{Namespace: "ns-1", Name: "pod-1", Value: "x", ResourceVersion: 2}, canon: false}}, rv: 2}
	in := Input{Kind: KUpdate, Key: "ns-1/pod-1", NoOp: true}
	_, o := mstep(in, st0)
	if o.RV != 3 {
		t.Fatalf("driver's model: RV %d, want 3", o.RV)
	}
	resp := correctness.Response{Object: &Obj{Namespace: "ns-1", Name: "pod-1", Value: "x", ResourceVersion: 3}}
	req := realRequest(in)
	for _, patched := range []bool{false, true} {
		m := initialModel(st0)
		if !patched {
			delete(m.NeedsRewrite, storeKey(in.Key))
		}
		ok, next, ch := m.Step(req, resp)
		t.Logf("patched %v: the Model accepts the rewrite: %v (change %v)", patched, ok, ch != nil)
		if ok != patched {
			t.Errorf("patched %v: got %v", patched, ok)
		}
		if ok && next.NeedsRewrite[storeKey(in.Key)] {
			t.Errorf("the rewrite leaves the key in NeedsRewrite")
		}
	}
}

// TestObjAccessors: Obj.SetResourceVersion parses the Model's decimal form ("" is 0, anything else
// leaves it), and ObjList is a metav1.ListInterface with the versioner's resource version.
func TestObjAccessors(t *testing.T) {
	o := &Obj{ResourceVersion: 9}
	for _, c := range []struct {
		s    string
		want uint64
	}{{"17", 17}, {"", 0}, {"x", 0}, {"18446744073709551615", 1<<64 - 1}, {"18446744073709551616", 1<<64 - 1}} {
		o.SetResourceVersion(c.s)
		if o.ResourceVersion != c.want {
			t.Errorf("SetResourceVersion(%q): %d, want %d", c.s, o.ResourceVersion, c.want)
		}
	}
	n := int64(4)
	l := &ObjList{ResourceVersion: 5, Continue: "c", RemainingItemCount: &n}
	acc, err := meta.ListAccessor(l)
	if err != nil {
		t.Fatal(err)
	}
	if acc.GetResourceVersion() != rvString(5) || acc.GetContinue() != "c" || *acc.GetRemainingItemCount() != 4 {
		t.Errorf("ListAccessor: %q %q %v", acc.GetResourceVersion(), acc.GetContinue(), acc.GetRemainingItemCount())
	}
	acc.SetResourceVersion(rvString(7))
	if l.ResourceVersion != 7 {
		t.Errorf("SetResourceVersion: %d", l.ResourceVersion)
	}
}

// TestFloor: with the floor, no drawn resource version of a Get, a List or a watch lies in
// [1, floor) (D7g-1), whatever the cached object.
func TestFloor(t *testing.T) {
	const floor = 3
	tbl := newWCache(1, 1<<40, floor)
	for _, crv := range []uint64{0, 1, 2, 3, 250} {
		tbl.put(0, Obj{Namespace: "ns-1", Name: "pod-1", ResourceVersion: crv})
		tbl.putW(1, Obj{Namespace: "ns-1", Name: "pod-1", ResourceVersion: crv})
		for i := 0; i < 20000; i++ {
			in := Gen(tbl, i%2)
			if in.MinRV == "" {
				continue
			}
			r, err := parseRV(in.MinRV)
			if err != nil {
				t.Fatalf("%+v: %v", in, err)
			}
			if r != 0 && r < floor {
				t.Fatalf("drawn RV %d below the floor: %+v", r, in)
			}
		}
	}
}

func bookmark(rv uint64) watch.Event {
	return watch.Event{Type: watch.Bookmark, Object: &Obj{ResourceVersion: rv, Annotated: true}}
}

// TestRealEvents: realEvents' cuts (D7g-2: after the first Error; D7g-3: a watch-list with no
// bookmark has no events).
func TestRealEvents(t *testing.T) {
	x := watch.Event{Type: watch.Added, Object: &Obj{Name: "x"}}
	e := watch.Event{Type: watch.Error, Object: &metav1.Status{Status: metav1.StatusFailure}}
	b := bookmark(3)
	cases := []struct {
		name     string
		sendInit int
		evs      []watch.Event
		want     int
	}{
		{"plain", 0, []watch.Event{x, x}, 2},
		{"error last", 0, []watch.Event{x, e}, 2},
		{"error in the middle", 0, []watch.Event{x, e, x, e}, 2},
		{"watch-list complete", 2, []watch.Event{x, b, x}, 3},
		{"watch-list error after bookmark", 2, []watch.Event{x, b, e, x}, 3},
		{"watch-list cut before bookmark", 2, []watch.Event{x, x}, 0},
		{"watch-list error before bookmark", 2, []watch.Event{x, e, b}, 0},
		{"not a watch-list, no bookmark", 1, []watch.Event{x}, 1},
	}
	for _, c := range cases {
		got := realEvents(Input{Kind: KWatch, SendInit: c.sendInit}, c.evs)
		if len(got) != c.want {
			t.Errorf("%s: %d events, want %d", c.name, len(got), c.want)
		}
	}
}
