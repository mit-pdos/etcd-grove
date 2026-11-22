package dist

import (
	"bytes"
	"encoding/json"
	"fmt"
	"math/rand/v2"
	"os"
	"os/exec"
	"path/filepath"
	"reflect"
	"strconv"
	"strings"
	"sync"
	"sync/atomic"
	"testing"
	"time"

	apierrors "k8s.io/apimachinery/pkg/api/errors"
	metav1 "k8s.io/apimachinery/pkg/apis/meta/v1"
	"k8s.io/apimachinery/pkg/watch"
	"k8s.io/apiserver/pkg/storage"

	etcddist "github.com/mit-pdos/etcd-grove/examples/etcd/dist/harness"
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
// kind of Raw: every value decodes to itself, a carried Raw is flagged RawOK, and one the
// encoding does not carry is flagged lost.
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

// addrs is the members' addresses of a cluster of machines ms: ports 2380 (peer) and 2379
// (client) of a machine's address in the namespace mode; in the local mode, ports of the one
// loopback address from base.
func addrs(n *robust.Network, ms []*robust.Machine, base int) func(int) (string, string) {
	return func(i int) (string, string) {
		if n.Namespaces() {
			return ms[i].IP + ":2380", ms[i].IP + ":2379"
		}
		return fmt.Sprintf("%s:%d", ms[i].IP, base+2*i), fmt.Sprintf("%s:%d", ms[i].IP, base+2*i+1)
	}
}

// TestWellFormed checks the deployment predicate on random deployments and on ill-formed ones.
func TestWellFormed(t *testing.T) {
	a := func(o int) func(int) (string, string) {
		return func(i int) (string, string) {
			return fmt.Sprintf("10.77.%d.1:2380", o+i+1), fmt.Sprintf("10.77.%d.1:2379", o+i+1)
		}
	}
	for n := 0; n < 50; n++ {
		if _, err := RandomDeployment("wf", 3, a(0), 3, a(3), FullSizes); err != nil {
			t.Fatalf("a random deployment is not well formed: %v", err)
		}
	}
	d, _ := RandomDeployment("wf", 3, a(0), 3, a(2), FullSizes)
	if WellFormed(d) == nil {
		t.Error("an address in both clusters passed")
	}
	d, _ = RandomDeployment("wf", 3, a(0), 1, a(3), FullSizes)
	bad := d
	bad.Store.Cfg.Retention = 10
	bad.Store.Cfg.CompactorMode = "revision"
	if WellFormed(bad) == nil {
		t.Error("etcd's compactor passed")
	}
	bad = d
	bad.StoreW.Apiservers = bad.StoreW.Clients + bad.StoreW.Watchers + 1
	if WellFormed(bad) == nil {
		t.Error("more API servers than clients passed")
	}
}

// run is one deployment's run: its processes beside the two clusters' members.
type run struct {
	d       Deployment
	cmd     etcddist.Command
	work    string
	c1, c2  *etcddist.Cluster
	lines   [2]string
	exited  [2]atomic.Bool
	ownFail chan error
}

// fail records a failure of the run's own processes.
func (r *run) fail(err error) {
	select {
	case r.ownFail <- err:
	default:
	}
}

// start starts a process on m with the arguments a, its log in logs/name.log; onExit (if not nil)
// is called if it ends without being killed, with its log's last lines.
func (r *run) start(m *robust.Machine, name string, a Args, onExit func(err error, tail string)) (*robust.Proc, string, error) {
	b, _ := json.Marshal(a)
	argPath := filepath.Join(r.work, name+".json")
	logPath := filepath.Join(r.work, "logs", name+".log")
	if err := os.WriteFile(argPath, b, 0o644); err != nil {
		return nil, "", err
	}
	lf, err := os.Create(logPath)
	if err != nil {
		return nil, "", err
	}
	p, err := m.Start(r.cmd.Path, []string{roleK8s, argPath}, r.cmd.Env, lf, func(err error) {
		lf.Sync()
		b, _ := os.ReadFile(logPath)
		ls := strings.Split(strings.TrimRight(string(b), "\n"), "\n")
		if len(ls) > 30 {
			ls = ls[len(ls)-30:]
		}
		onExit(err, strings.Join(ls, "\n"))
	})
	if err != nil {
		lf.Close()
		return nil, "", err
	}
	go func() {
		<-p.Exited()
		lf.Close()
	}()
	return p, argPath, nil
}

// deployRound runs one random deployment: the store's cluster of k1 members and the compactor's
// of k2, each workload's API server (or writer) machines and its orchestrator, under the faults
// once both orchestrators' set-ups are done; it fails t on a failure.
func deployRound(t *testing.T, round int, netns bool, crash string, k1, k2 int, sz Sizes, deadline time.Duration) {
	exe, err := os.Executable()
	if err != nil {
		t.Fatal(err)
	}
	n, err := etcddist.NewNet(netns)
	if err != nil {
		t.Fatal(err)
	}
	defer n.Close()
	var ms1, ms2 []*robust.Machine
	for i := 0; i < k1; i++ {
		m, err := n.AddMachine(fmt.Sprintf("store-member-%d", i))
		if err != nil {
			t.Fatal(err)
		}
		ms1 = append(ms1, m)
	}
	for i := 0; i < k2; i++ {
		m, err := n.AddMachine(fmt.Sprintf("compactor-member-%d", i))
		if err != nil {
			t.Fatal(err)
		}
		ms2 = append(ms2, m)
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
	d, err := RandomDeployment(tag, k1, addrs(n, ms1, base), k2, addrs(n, ms2, base+2*k1), sz)
	if err != nil {
		t.Fatalf("%v: %v", d, err)
	}
	cfg := etcddist.Config{Crash: crash, CrashPause: 2 * time.Second, Downtime: time.Second, Netns: netns,
		NetPause: time.Second, NetHold: 2 * time.Second, Deadline: deadline, SetupWait: setupWait}
	cfg2 := cfg
	cfg2.NetPause = 0 // one nemesis, over every machine: the store cluster's (RunFaults)
	work, err := os.MkdirTemp("", "k8sdist-")
	if err != nil {
		t.Fatal(err)
	}
	if err := os.MkdirAll(filepath.Join(work, "logs"), 0o755); err != nil {
		t.Fatal(err)
	}
	r := &run{d: d, cmd: etcddist.Command{Path: exe, Env: []string{"DIST_PROC=1"}}, work: work,
		ownFail: make(chan error, 1)}
	start := time.Now()
	r.c1, err = etcddist.Start(d.Store, cfg, r.cmd, filepath.Join(work, "store"), n, ms1)
	if err != nil {
		t.Fatalf("%v: %v", d, err)
	}
	r.c2, err = etcddist.Start(d.Compactor, cfg2, r.cmd, filepath.Join(work, "compactor"), n, ms2)
	if err != nil {
		r.c1.Stop()
		t.Fatalf("%v: %v", d, err)
	}
	res := r.runClients(n, append(append([]*robust.Machine{}, ms1...), ms2...), deadline)
	r.c1.Stop()
	r.c2.Stop()
	t.Logf("round %d: %v (%v)\n  store cluster: %s\n  compactor cluster: %s\n  network: %s\n  %s\n  %s", round, d,
		time.Since(start).Round(time.Second), &r.c1.Stats, &r.c2.Stats, r.c1.NetStats(), r.lines[0], r.lines[1])
	if res != nil {
		t.Errorf("round %d: %v (work directory kept: %s)", round, res, work)
		return
	}
	os.RemoveAll(work)
}

// runClients starts the workloads' client machines (the store's API servers, the compactor's
// writer and API servers) and orchestrators, holds the faults until both orchestrators have
// marked their set-up done (or ended, or SetupWait passed), then makes them (both clusters'
// crashes, one network nemesis over every machine) until both orchestrators are done, the deadline
// passes or the run fails. It returns the run's first failure, nil if none.
func (r *run) runClients(n *robust.Network, members []*robust.Machine, deadline time.Duration) error {
	all := append([]*robust.Machine{}, members...)
	var nodeProcs []*robust.Proc
	defer func() {
		for _, p := range nodeProcs {
			p.Kill()
		}
	}()
	localPort := 31000 + 20*rand.IntN(80)
	ws := []Workload{r.d.StoreW, r.d.CompW}
	epss := [][]string{r.d.Store.Endpoints(), r.d.Compactor.Endpoints()}
	var orchMs []*robust.Machine
	var wAddrs [][]string
	for i, w := range ws {
		om, err := n.AddMachine(fmt.Sprintf("orch-%s", w.Kind))
		if err != nil {
			return err
		}
		orchMs = append(orchMs, om)
		all = append(all, om)
		var nms []*robust.Machine
		for j := 0; j < NodeCount(w); j++ {
			nm, err := n.AddMachine(fmt.Sprintf("%s-node-%d", w.Kind, j))
			if err != nil {
				return err
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
		wAddrs = append(wAddrs, as)
		for j, nm := range nms {
			name := fmt.Sprintf("%s-node-%d", w.Kind, j)
			p, _, err := r.start(nm, name, Args{W: w, Eps: epss[i], Addrs: as, IsNode: true, Node: j},
				func(err error, tail string) {
					r.fail(fmt.Errorf("%s's machine exited (%v); its log:\n%s", name, err, tail))
				})
			if err != nil {
				return err
			}
			nodeProcs = append(nodeProcs, p)
		}
	}
	done := make(chan int, 2)
	var procs []*robust.Proc
	var paths []string
	for i, w := range ws {
		name := fmt.Sprintf("orch-%s", w.Kind)
		p, path, err := r.start(orchMs[i], name, Args{W: w, Eps: epss[i], Addrs: wAddrs[i]},
			func(err error, tail string) {
				if err != nil {
					r.fail(fmt.Errorf("%s failed (%v); its log:\n%s", name, err, tail))
				}
				ls := strings.Split(tail, "\n")
				r.lines[i] = strings.TrimSpace(ls[len(ls)-1])
				r.exited[i].Store(true)
				done <- i
			})
		if err != nil {
			return err
		}
		procs = append(procs, p)
		paths = append(paths, path)
	}
	defer func() {
		for _, p := range procs {
			p.Kill()
		}
	}()
	stop := make(chan struct{})
	var wg sync.WaitGroup
	wg.Add(1)
	go func() {
		defer wg.Done()
		t0 := time.Now()
		limit := t0.Add(setupWait)
		for {
			ok, all2 := 0, true
			for i, p := range paths {
				if _, err := os.Stat(p + ".ready"); err == nil {
					ok++
				} else if !r.exited[i].Load() {
					all2 = false
				}
			}
			if all2 || time.Now().After(limit) {
				for _, c := range []*etcddist.Cluster{r.c1, r.c2} {
					c.Stats.SetupsDone.Store(int64(ok))
					c.Stats.FaultsAfter.Store(int64(time.Since(t0)))
				}
				break
			}
			select {
			case <-stop:
				return
			case <-time.After(100 * time.Millisecond):
			}
		}
		wg.Add(2)
		go func() { r.c1.RunFaults(all, stop); wg.Done() }()
		go func() { r.c2.RunFaults(nil, stop); wg.Done() }()
	}()
	var err error
	timeout := time.After(deadline)
	for k := 0; k < len(procs) && err == nil; k++ {
		select {
		case <-done:
		case <-timeout:
			err = fmt.Errorf("the orchestrators were not done after %v", deadline)
		case e := <-r.ownFail:
			err = e
		case <-r.c1.Failed():
			err = r.c1.Err()
		case <-r.c2.Failed():
			err = r.c2.Err()
		}
	}
	if err == nil {
		select {
		case e := <-r.ownFail:
			err = e
		default:
		}
	}
	close(stop)
	wg.Wait()
	if err == nil {
		err = r.c1.Err()
	}
	if err == nil {
		err = r.c2.Err()
	}
	return err
}

// setupWait is how long the faults wait for the orchestrators' set-ups (etcd-dist's SetupWait).
const setupWait = 3 * time.Minute

// TestDist runs random deployments of k8s_safe's program as a distributed deployment: the
// store's cluster and the compactor's, three members each, every member and
// every Kubernetes component on a machine of its own, while members crash (kills, and power
// losses where the device mapper is available) and, on network namespaces, the network fails. It
// runs only with DIST_RUN set; -short runs one small deployment, otherwise DIST_ROUNDS (default 4).
// DIST_OPS=n sets the store's clients' operations, DIST_ROUNDS_C=n the compactor's rounds. Faults start once both orchestrators' set-ups
// are done. A root without CAP_NET_ADMIN (a container) runs the test again in a user namespace of
// its own (the bridge variant); a non-root runs it again by sudo -n if it can, and in the local
// mode (one loopback address, no network faults) otherwise.
func TestDist(t *testing.T) {
	if os.Getenv("DIST_RUN") == "" {
		t.Skip("set DIST_RUN=1 to run (minutes per deployment; namespaces need root)")
	}
	netns := robust.NetnsAvailable() == nil
	if !netns && os.Getenv("DIST_CHILD") == "" {
		args := []string{"-test.run=^TestDist$", "-test.v", "-test.count=1", "-test.timeout=3h"}
		if testing.Short() {
			args = append(args, "-test.short")
		}
		var rerun func([]string, []string, *bytes.Buffer) error
		if robust.IsRoot() {
			rerun = func(a, e []string, out *bytes.Buffer) error { return robust.RerunInUserns(a, e, out) }
		} else if exec.Command("sudo", "-n", "true").Run() == nil {
			rerun = func(a, e []string, out *bytes.Buffer) error { return robust.RerunAsRoot(a, e, out) }
		}
		if rerun != nil {
			var out bytes.Buffer
			err := rerun(args, []string{"DIST_RUN=1", "DIST_CHILD=1", "DIST_ROUNDS=" + os.Getenv("DIST_ROUNDS"),
				"DIST_OPS=" + os.Getenv("DIST_OPS"), "DIST_ROUNDS_C=" + os.Getenv("DIST_ROUNDS_C")}, &out)
			for _, l := range strings.Split(out.String(), "\n") {
				if strings.TrimSpace(l) != "" {
					t.Log(l)
				}
			}
			if err != nil {
				t.Fatalf("in the namespaces' child: %v", err)
			}
			return
		}
	}
	crash := etcddist.CrashKill
	if robust.PowerAvailable() == nil {
		crash = etcddist.CrashMixed
	}
	if testing.Short() {
		deployRound(t, 1, netns, crash, 3, 3, ShortSizes, 8*time.Minute)
		return
	}
	rounds := 4
	if s := os.Getenv("DIST_ROUNDS"); s != "" {
		if v, err := strconv.Atoi(s); err == nil && v > 0 {
			rounds = v
		}
	}
	for i := 1; i <= rounds && !t.Failed(); i++ {
		deployRound(t, i, netns, crash, 3, 3, FullSizes, 15*time.Minute)
	}
}
