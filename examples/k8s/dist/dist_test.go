package dist

import (
	"bytes"
	"encoding/json"
	"fmt"
	"math/rand/v2"
	"os"
	"path/filepath"
	"reflect"
	"strconv"
	"strings"
	"testing"
	"time"

	apierrors "k8s.io/apimachinery/pkg/api/errors"
	metav1 "k8s.io/apimachinery/pkg/apis/meta/v1"
	"k8s.io/apimachinery/pkg/watch"
	"k8s.io/apiserver/pkg/storage"

	etcddist "github.com/mit-pdos/etcd-grove/examples/etcd/dist"
	"github.com/mit-pdos/etcd-grove/examples/lib/robust"

	comp "github.com/mit-pdos/etcd-grove/examples/k8s/dist/compactorcopy"
	k8s "github.com/mit-pdos/etcd-grove/examples/k8s/dist/storecopy"
)

// The role of a k8s client machine's process (a member's is etcd-dist's server role).
const roleK8s = "k8s"

// runProcess runs a process of a deployment: a member (etcd-dist's server role: server.Main), or
// a k8s client machine (roleK8s with an Args JSON file): an orchestrator (MainReady, its result
// printed, its set-up done marked by FILE.ready) or a client machine (NodeMain, which never
// returns).
func runProcess(args []string) error {
	if len(args) != 2 {
		return fmt.Errorf("usage: server|k8s FILE.json")
	}
	if args[0] != roleK8s {
		return etcddist.RunProcess(args)
	}
	b, err := os.ReadFile(args[1])
	if err != nil {
		return err
	}
	var a Args
	if err := json.Unmarshal(b, &a); err != nil {
		return err
	}
	if a.IsNode {
		NodeMain(a.W, a.Node, a.Addrs, a.Eps)
		return fmt.Errorf("NodeMain returned")
	}
	ready := func() { os.WriteFile(args[1]+".ready", nil, 0o644) }
	fmt.Printf("%s: %v\n", a.W.Kind, MainReady(a.W, a.Eps, a.Addrs, ready))
	return nil
}

// TestMain runs a process of a deployment instead of the tests when this binary was started as one
// (DIST_PROC set).
func TestMain(m *testing.M) {
	if os.Getenv("DIST_PROC") != "" {
		if err := runProcess(os.Args[1:]); err != nil {
			fmt.Fprintln(os.Stderr, err)
			os.Exit(2)
		}
		os.Exit(0)
	}
	os.Exit(m.Run())
}

// TestVerbatim checks that the copies (storecopy, compactorcopy) are the drivers' files byte for
// byte, so that the distributed workloads run the code k8s_safe is proved about.
func TestVerbatim(t *testing.T) {
	for _, c := range []struct{ dir, from string }{
		{"storecopy", "../etcd3"}, {"compactorcopy", "../compactor"},
	} {
		srcs, _ := filepath.Glob(filepath.Join(c.from, "*.go"))
		n := 0
		for _, src := range srcs {
			if strings.HasSuffix(src, "_test.go") {
				continue
			}
			n++
			want, err := os.ReadFile(src)
			if err != nil {
				t.Fatal(err)
			}
			got, err := os.ReadFile(filepath.Join(c.dir, filepath.Base(src)))
			if err != nil {
				t.Fatalf("%s has no copy: %v", src, err)
			}
			if !bytes.Equal(got, want) {
				t.Errorf("%s/%s differs from %s", c.dir, filepath.Base(src), src)
			}
		}
		if n == 0 {
			t.Errorf("no source in %s", c.from)
		}
		copies, _ := filepath.Glob(filepath.Join(c.dir, "*.go"))
		if len(copies) != n+1 {
			t.Errorf("%s: %d files, want the %d copies and export.go", c.dir, len(copies), n)
		}
	}
}

// TestStoreCodec checks the store workload's wire on random inputs and on outputs carrying each
// kind of Raw: every value decodes to itself, a carried Raw is flagged RawOK, one the encoding
// does not carry is flagged lost, and etcd's "compacted" (a List's error, a watch's Error event) is
// flagged Compacted.
func TestStoreCodec(t *testing.T) {
	str := func() string { return strconv.Itoa(rand.IntN(1000)) }
	obj := func() k8s.Obj {
		return k8s.Obj{Namespace: str(), Name: str(), UID: str(), Value: str(), Node: str(), App: str(),
			ResourceVersion: rand.Uint64(), Annotated: rand.IntN(2) == 0}
	}
	for i := 0; i < 200; i++ {
		in := k8s.Input{Kind: rand.IntN(6), Key: str(), Val: str(), Node: str(), App: str(),
			HasReject: rand.IntN(2) == 0, Reject: str(), NoOp: true, IgnoreNotFound: rand.IntN(2) == 0,
			UID: str(), HasPreUID: true, PreUID: str(), HasPreRV: true, PreRV: str(), UseCached: true,
			Cached: obj(), MinRV: str(), ListKey: str(), Recursive: true, Match: 2, Field: 5, SelNS: str(),
			SelName: str(), SelNode: str(), SelApp: str(), Limit: rand.Int64(), Client: rand.IntN(9),
			WKey: str(), SendInit: 2, Bookmarks: true, Behavior: 3, Skip: rand.IntN(2) == 0}
		got, ok := DecInput(EncInput(in))
		if !ok || !reflect.DeepEqual(got, in) {
			t.Fatalf("input %+v decodes to %+v (%v)", in, got, ok)
		}
		if _, ok := DecInput(append(EncInput(in), 0)); ok {
			t.Fatal("an extended input decoded")
		}
	}
	del, upd := k8s.Rejections()
	o, l := obj(), &k8s.ObjList{Items: []k8s.Obj{}, ResourceVersion: 7, Continue: "c"}
	rem := int64(3)
	l2 := &k8s.ObjList{Items: []k8s.Obj{obj(), obj()}, RemainingItemCount: &rem}
	carried := []k8s.Raw{
		{},
		{Object: &o},
		{Object: l},
		{Object: l2},
		{Object: &k8s.ObjList{}},
		{Err: storage.NewKeyNotFoundError("/registry/objs/a", 5)},
		{Err: storage.NewKeyExistsError("/registry/objs/a", 0)},
		{Err: storage.NewInvalidObjError("/registry/objs/a", "Precondition failed: UID in precondition: x, UID in object meta: y")},
		{Err: storage.NewTooLargeResourceVersionError(10, 5, 1)},
		{Err: del},
		{Err: upd},
		{Events: []watch.Event{{Type: watch.Added, Object: &o},
			{Type: watch.Bookmark, Object: &k8s.Obj{ResourceVersion: 9, Annotated: true}},
			{Type: watch.Error, Object: &metav1.Status{Status: metav1.StatusFailure, Message: "m", Code: 410}}}},
		{Events: []watch.Event{}},
	}
	for _, r := range carried {
		out := k8s.Output{Err: k8s.ENotFound, ErrKey: str(), ErrRV: 3, ErrMsg: str(), Name: str(), RV: 4,
			Items: str(), ListRV: 6, Continue: str(), HasRemaining: true, Remaining: 2, WEvents: str(), Raw: r}
		so, ok := DecOutput(EncStoreOut(out))
		if !ok || !so.RawOK || !reflect.DeepEqual(so.Out, out) {
			t.Errorf("raw %+v: decoded %+v, RawOK %v, ok %v", r, so.Out.Raw, so.RawOK, ok)
		}
	}
	expired := apierrors.NewResourceExpired("The resourceVersion for the provided list is too old.")
	wexpired := expired.Status()
	for _, c := range []struct {
		r    k8s.Raw
		comp bool
	}{
		{k8s.Raw{Err: expired}, true},
		{k8s.Raw{Events: []watch.Event{{Type: watch.Added, Object: &o}, {Type: watch.Error, Object: &wexpired}}}, true},
		{k8s.Raw{Err: storage.NewKeyNotFoundError("/registry/objs/a", 5)}, false},
		{k8s.Raw{Events: []watch.Event{{Type: watch.Error, Object: &metav1.Status{Status: metav1.StatusFailure, Code: 500}}}}, false},
	} {
		so, ok := DecOutput(EncStoreOut(k8s.Output{Err: k8s.EOther, Raw: c.r}))
		if !ok || so.Compacted != c.comp {
			t.Errorf("raw %+v: Compacted %v, want %v (ok %v)", c.r, so.Compacted, c.comp, ok)
		}
	}
	for _, r := range []k8s.Raw{{Err: fmt.Errorf("other")}, {Err: apierrors.NewBadRequest("x"), Object: &metav1.List{}}} {
		so, ok := DecOutput(EncStoreOut(k8s.Output{Raw: r}))
		if !ok || so.RawOK {
			t.Errorf("raw %+v: RawOK %v, ok %v; want lost", r, so.RawOK, ok)
		}
	}
}

// TestCompactorCodec checks the compactor workload's logs round-trip.
func TestCompactorCodec(t *testing.T) {
	ls := []comp.Log{{Samples: []int64{1, 2, 3}, Stopped: 3, Get1: true, Rev1: 9, HasKey: true, Value: "4",
		Get2: true, Rev2: 10}, {}}
	c := compactorCodec()
	got, ok := c.DecOut(c.EncOut(ls))
	if !ok || !reflect.DeepEqual(got, ls) {
		t.Fatalf("logs %+v decode to %+v (%v)", ls, got, ok)
	}
	if n, ok := c.DecIn(c.EncIn(3)); !ok || n != 3 {
		t.Fatal("index")
	}
}

// TestCheckLog checks that CheckLog makes check's comparisons: each failing log panics.
func TestCheckLog(t *testing.T) {
	comp.CheckLog(comp.Log{Samples: []int64{0, 2, 2}, Stopped: 2, Get1: true, Rev1: 5, HasKey: true,
		Value: "2", Get2: true, Rev2: 5})
	for _, l := range []comp.Log{
		{Samples: []int64{3, 2}},
		{Samples: []int64{3}, Stopped: 2},
		{Stopped: 6, Get1: true, Rev1: 5},
		{Get1: true, Rev1: 5, HasKey: true, Value: "x"},
		{Get1: true, Rev1: 5, HasKey: true, Value: "7", Get2: true, Rev2: 6},
	} {
		func() {
			defer func() {
				if recover() == nil {
					t.Errorf("log %+v passed", l)
				}
			}()
			comp.CheckLog(l)
		}()
	}
}

// TestWellFormed checks the deployment predicate on random deployments and on ill-formed ones.
func TestWellFormed(t *testing.T) {
	a := func(i int) (string, string) {
		return fmt.Sprintf("10.77.%d.1:2380", i+1), fmt.Sprintf("10.77.%d.1:2379", i+1)
	}
	for n := 0; n < 50; n++ {
		if _, err := RandomDeployment("wf", 3, a, FullSizes); err != nil {
			t.Fatalf("a random deployment is not well formed: %v", err)
		}
	}
	d, _ := RandomDeployment("wf", 3, a, FullSizes)
	bad := d
	bad.Cluster.Cfg.Retention = 10
	bad.Cluster.Cfg.CompactorMode = "revision"
	if WellFormed(bad) == nil {
		t.Error("etcd's compactor passed")
	}
	bad = d
	bad.StoreW.Apiservers = bad.StoreW.Clients + bad.StoreW.Watchers + 1
	if WellFormed(bad) == nil {
		t.Error("more API servers than clients passed")
	}
	bad = d
	bad.CompW.Rounds = 0
	if WellFormed(bad) == nil {
		t.Error("no compactor round passed")
	}
}

// writeArgs writes a's JSON file for the process named name, and returns its path.
func writeArgs(work, name string, a Args) (string, error) {
	b, _ := json.Marshal(a)
	p := filepath.Join(work, name+".json")
	return p, os.WriteFile(p, b, 0o644)
}

// deployRound runs one random deployment: the cluster of k members (a group of restartables of
// one robust.Run, crashed by its crasher), both workloads' API server (and writer) machines and
// their orchestrators against it, under the faults (the crashes, and one network nemesis over every
// machine) once both orchestrators' set-ups are done; it fails t on a failure.
func deployRound(t *testing.T, round int, netns bool, crash string, k int, sz Sizes, deadline time.Duration) {
	exe, err := os.Executable()
	if err != nil {
		t.Fatal(err)
	}
	n, err := robust.NewNetworkOrLocal(netns, "ed")
	if err != nil {
		t.Fatal(err)
	}
	defer n.Close()
	var ms []*robust.Machine
	for i := 0; i < k; i++ {
		m, err := n.AddMachine(fmt.Sprintf("member-%d", i))
		if err != nil {
			t.Fatal(err)
		}
		ms = append(ms, m)
	}
	base := 20000 + 2*rand.IntN(4000)
	if s := os.Getenv("DIST_OPS"); s != "" {
		if v, err := strconv.Atoi(s); err == nil && v > 0 {
			sz.Ops = v
		}
	}
	if s := os.Getenv("DIST_ROUNDS_C"); s != "" {
		if v, err := strconv.Atoi(s); err == nil && v > 0 {
			sz.Rounds = v
		}
	}
	tag := fmt.Sprintf("k%d-%d", os.Getpid(), round)
	d, err := RandomDeployment(tag, k, etcddist.MemberAddrs(n, ms, base), sz)
	if err != nil {
		t.Fatalf("%v: %v", d, err)
	}
	cfg := robust.Config{Crash: crash, CrashPause: 2 * time.Second, Downtime: time.Second, Netns: netns,
		NetPause: time.Second, NetHold: 2 * time.Second, Deadline: deadline, SetupWait: 3 * time.Minute}
	work, err := os.MkdirTemp("", "k8sdist-")
	if err != nil {
		t.Fatal(err)
	}
	start := time.Now()
	r, err := robust.NewRun(cfg, robust.Command{Path: exe, Env: []string{"DIST_PROC=1"}}, n, work)
	if err != nil {
		t.Fatal(err)
	}
	var lines []string
	c, err := etcddist.Start(d.Cluster, r, n, ms)
	if err == nil {
		lines, err = runClients(r, n, d, ms)
	}
	if err == nil {
		err = r.Err()
	}
	r.Stop()
	if c != nil {
		c.Stop()
	}
	for len(lines) < 2 {
		lines = append(lines, "")
	}
	t.Logf("round %d: %v (%v)\n  %s; network: %s\n  %s\n  %s", round, d,
		time.Since(start).Round(time.Second), &r.Stats, r.NetStats(), lines[0], lines[1])
	if err != nil {
		t.Errorf("round %d: %v (work directory kept: %s)", round, err, work)
		return
	}
	os.RemoveAll(work)
}

// runClients makes the workloads' machines and runs their processes in r (robust.Run.RunClients):
// the client machines (the store's API servers, the compactor's writer and API servers), then the
// orchestrators, every one against the one cluster, the network faults over every machine (the
// members' and these). It returns the orchestrators' result lines (the store's, the compactor's).
func runClients(r *robust.Run, n *robust.Network, d Deployment, members []*robust.Machine) ([]string, error) {
	all := append([]*robust.Machine{}, members...)
	localPort := 31000 + 20*rand.IntN(80)
	eps := d.Cluster.Endpoints()
	var nodes, orchs []robust.Client
	for _, w := range []Workload{d.StoreW, d.CompW} {
		om, err := n.AddMachine(fmt.Sprintf("orch-%s", w.Kind))
		if err != nil {
			return nil, err
		}
		all = append(all, om)
		var nms []*robust.Machine
		for j := 0; j < NodeCount(w); j++ {
			nm, err := n.AddMachine(fmt.Sprintf("%s-node-%d", w.Kind, j))
			if err != nil {
				return nil, err
			}
			nms = append(nms, nm)
			all = append(all, nm)
		}
		var as []string
		for c := 0; c < AddrCount(w); c++ {
			nm := nms[c%len(nms)]
			if n.Namespaces() {
				as = append(as, nm.IP+":"+strconv.Itoa(etcddist.NodePort+c))
			} else {
				as = append(as, fmt.Sprintf("%s:%d", nm.IP, localPort))
				localPort++
			}
		}
		for j, nm := range nms {
			name := fmt.Sprintf("%s-node-%d", w.Kind, j)
			p, err := writeArgs(r.Work(), name, Args{W: w, Eps: eps, Addrs: as, IsNode: true, Node: j})
			if err != nil {
				return nil, err
			}
			nodes = append(nodes, robust.Client{Name: name, Machine: nm, Args: []string{roleK8s, p}})
		}
		name := fmt.Sprintf("orch-%s", w.Kind)
		p, err := writeArgs(r.Work(), name, Args{W: w, Eps: eps, Addrs: as})
		if err != nil {
			return nil, err
		}
		orchs = append(orchs, robust.Client{Name: name, Machine: om, Args: []string{roleK8s, p}, Ready: p + ".ready"})
	}
	return r.RunClients(nodes, orchs, all), nil
}

// TestDist runs random deployments of k8s_safe's workloads as a distributed deployment over one
// cluster of three members (where k8s_safe's program has two), every member and
// every Kubernetes component on a machine of its own, while members crash (kills, and power
// losses where the device mapper is available) and, on network namespaces, the network fails. It
// runs only with DIST_RUN set; -short runs one small deployment, otherwise DIST_ROUNDS (default 4).
// DIST_OPS=n sets the store's clients' operations, DIST_ROUNDS_C=n the compactor's rounds. Faults start once both orchestrators' set-ups
// are done. Without network namespaces, the test runs again where it can make them
// (robust.RerunTest: a container's root in a user namespace of its own, a non-root by sudo -n), and
// in the local mode (one loopback address, no network faults) if it cannot.
func TestDist(t *testing.T) {
	if os.Getenv("DIST_RUN") == "" {
		t.Skip("set DIST_RUN=1 to run (minutes per deployment; namespaces need root)")
	}
	if robust.RerunTest(t, "TestDist", "3h", testing.Short(), []string{"DIST_RUN=1",
		"DIST_ROUNDS=" + os.Getenv("DIST_ROUNDS"), "DIST_OPS=" + os.Getenv("DIST_OPS"),
		"DIST_ROUNDS_C=" + os.Getenv("DIST_ROUNDS_C")}) {
		return
	}
	netns := robust.NetnsAvailable() == nil
	crash := robust.CrashKill
	if robust.PowerAvailable() == nil {
		crash = robust.CrashMixed
	}
	if testing.Short() {
		deployRound(t, 1, netns, crash, 3, ShortSizes, 8*time.Minute)
		return
	}
	rounds := 4
	if s := os.Getenv("DIST_ROUNDS"); s != "" {
		if v, err := strconv.Atoi(s); err == nil && v > 0 {
			rounds = v
		}
	}
	for i := 1; i <= rounds && !t.Failed(); i++ {
		deployRound(t, i, netns, crash, 3, FullSizes, 15*time.Minute)
	}
}
