package dist

import (
	"encoding/json"
	"fmt"
	"math/rand/v2"
	"os"
	"path/filepath"
	"reflect"
	"strconv"
	"testing"
	"time"

	apierrors "k8s.io/apimachinery/pkg/api/errors"
	metav1 "k8s.io/apimachinery/pkg/apis/meta/v1"
	"k8s.io/apimachinery/pkg/watch"
	"k8s.io/apiserver/pkg/storage"

	etcddist "github.com/mit-pdos/etcd-grove/examples/etcd/dist"
	"github.com/mit-pdos/etcd-grove/examples/lib/robust"

	comp "github.com/mit-pdos/etcd-grove/examples/k8s/compactor"
	k8s "github.com/mit-pdos/etcd-grove/examples/k8s/etcd3"
)

// The role of a k8s client machine's process (a member's is etcd-dist's server role).
const roleK8s = "k8s"

// procArgs is a k8s client machine's process configuration (the JSON file of roleK8s): the
// deployment, and which machine: the orchestrator of workload Index, or (IsNode) the Index-th
// client machine.
type procArgs struct {
	D      Deployment
	IsNode bool
	Index  int
}

// runProcess runs a process of a deployment: a member (etcd-dist's server role: server.Main), or
// a k8s client machine (roleK8s with a procArgs JSON file): an orchestrator (MainDeployment, its
// result printed, its set-up done marked by FILE.ready; Orchestrator but for the marker and the
// line) or a client machine (NodeDeployment, which never returns).
func runProcess(args []string) error {
	if len(args) == 0 || args[0] != roleK8s {
		return etcddist.RunProcess(args)
	}
	if len(args) != 2 {
		return fmt.Errorf("usage: k8s FILE.json")
	}
	b, err := os.ReadFile(args[1])
	if err != nil {
		return err
	}
	var a procArgs
	if err := json.Unmarshal(b, &a); err != nil {
		return err
	}
	if a.IsNode {
		NodeDeployment(a.D, a.Index)
		return fmt.Errorf("NodeDeployment returned")
	}
	w, _, _ := a.D.Workload(a.Index)
	ready := func() { os.WriteFile(args[1]+".ready", nil, 0o644) }
	fmt.Printf("%s: %v\n", w.Kind, MainDeployment(a.D, a.Index, ready))
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
	nodes := func(w Workload) []string {
		var as []string
		for c := 0; c < AddrCount(w); c++ {
			as = append(as, fmt.Sprintf("10.78.%d.%d:%d", int(w.Kind), c+1, etcddist.NodePort))
		}
		return as
	}
	for n := 0; n < 50; n++ {
		if _, err := RandomDeployment("wf", 3, a, FullSizes, nodes); err != nil {
			t.Fatalf("a random deployment is not well formed: %v", err)
		}
	}
	d, _ := RandomDeployment("wf", 3, a, FullSizes, nodes)
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
	bad = d
	bad.CompAddrs = append([]string{}, d.CompAddrs...)
	bad.CompAddrs[1] = d.StoreAddrs[0]
	if WellFormed(bad) == nil {
		t.Error("a client machine address used twice passed")
	}
	bad.CompAddrs[1] = d.Cluster.Members[0].Client
	if WellFormed(bad) == nil {
		t.Error("a member's address as a client machine's passed")
	}
	bad.CompAddrs = d.CompAddrs[1:]
	if WellFormed(bad) == nil {
		t.Error("a missing client machine address passed")
	}
	for n := 0; n < NodeCount(d.StoreW)+NodeCount(d.CompW); n++ {
		j, c, ok := d.Node(n)
		if w, _, _ := d.Workload(j); !ok || c >= NodeCount(w) {
			t.Errorf("Node(%d) = %d, %d, %v", n, j, c, ok)
		}
	}
	if _, _, ok := d.Node(NodeCount(d.StoreW) + NodeCount(d.CompW)); ok {
		t.Error("a client machine past the last")
	}
}

// writeArgs writes a's JSON file for the process named name, and returns its path.
func writeArgs(work, name string, a procArgs) (string, error) {
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
	cm := &clientMachines{n: n, localPort: 31000 + 20*rand.IntN(80)}
	d, err := RandomDeployment(tag, k, etcddist.MemberAddrs(n, ms, base), sz, cm.addrs)
	if cm.err != nil {
		t.Fatal(cm.err)
	}
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
	c, err := etcddist.Start(d.Cluster, r, n, ms, nil)
	if err == nil {
		lines, err = runClients(r, cm, d, ms)
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

// clientMachines makes the workloads' machines on n as RandomDeployment asks for their addresses
// (addrs): per workload, its orchestrator's machine and its client machines, client c's address on
// client machine c mod NodeCount (NodePort+c on network namespaces, a port of its own from
// localPort on in the local mode).
type clientMachines struct {
	n         *robust.Network
	localPort int
	orch      []*robust.Machine
	nodes     [][]*robust.Machine
	err       error
}

func (cm *clientMachines) addrs(w Workload) []string {
	if cm.err != nil {
		return nil
	}
	om, err := cm.n.AddMachine(fmt.Sprintf("orch-%s", w.Kind))
	if err != nil {
		cm.err = err
		return nil
	}
	var nms []*robust.Machine
	for j := 0; j < NodeCount(w); j++ {
		nm, err := cm.n.AddMachine(fmt.Sprintf("%s-node-%d", w.Kind, j))
		if err != nil {
			cm.err = err
			return nil
		}
		nms = append(nms, nm)
	}
	cm.orch = append(cm.orch, om)
	cm.nodes = append(cm.nodes, nms)
	var as []string
	for c := 0; c < AddrCount(w); c++ {
		nm := nms[c%len(nms)]
		if cm.n.Namespaces() {
			as = append(as, nm.IP+":"+strconv.Itoa(etcddist.NodePort+c))
		} else {
			as = append(as, fmt.Sprintf("%s:%d", nm.IP, cm.localPort))
			cm.localPort++
		}
	}
	return as
}

// runClients runs the processes of the workloads' machines (cm's) in r (robust.Run.RunClients):
// the client machines (the store's API servers, the compactor's writer and API servers:
// NodeDeployment), then the orchestrators (MainDeployment), every one against the one cluster, the
// network faults over every machine (the members' and these). It returns the orchestrators' result
// lines (the store's, the compactor's).
func runClients(r *robust.Run, cm *clientMachines, d Deployment, members []*robust.Machine) ([]string, error) {
	all := append([]*robust.Machine{}, members...)
	var nodes, orchs []robust.Client
	n := 0
	for j := range cm.orch {
		w, _, _ := d.Workload(j)
		all = append(all, cm.orch[j])
		for c, nm := range cm.nodes[j] {
			all = append(all, nm)
			name := fmt.Sprintf("%s-node-%d", w.Kind, c)
			p, err := writeArgs(r.Work(), name, procArgs{D: d, IsNode: true, Index: n})
			if err != nil {
				return nil, err
			}
			n++
			nodes = append(nodes, robust.Client{Name: name, Machine: nm, Args: []string{roleK8s, p}})
		}
		name := fmt.Sprintf("orch-%s", w.Kind)
		p, err := writeArgs(r.Work(), name, procArgs{D: d, Index: j})
		if err != nil {
			return nil, err
		}
		orchs = append(orchs, robust.Client{Name: name, Machine: cm.orch[j], Args: []string{roleK8s, p}, Ready: p + ".ready"})
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
		"DIST_ROUNDS_C=" + os.Getenv("DIST_ROUNDS_C"), "DIST_DUMP=" + os.Getenv("DIST_DUMP")}) {
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
