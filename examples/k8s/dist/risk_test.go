package dist

// The three risk tests of K8's scope (notes/k8s-dist-k8-scope.md, §3 risks 1-3), each run in a
// child process of its own (riskChild: a fresh one-member etcd per run, its files removed after):
//
//   - TestCompactedProvenance: a client compacts at the current revision every millisecond while
//     the store runs Gen's operations of every kind; a compacted answer (compacted(raw)) comes only
//     on an input that PastRead or PinnedRead holds of.
//   - TestForeignHeavy: a foreign writer (a key under /k8sdist-compactor/, outside /registry/)
//     writes 10 revisions per store operation, throughout the run or only from the end of the
//     unary operations on: CheckShared is Ok, and RealCheck is Ok on a history NoForeign holds of.
//   - TestRealCheckShifted: one sequence of inputs run on a cluster seeded at 2 and 3 and,
//     renumbered, on one seeded at 5 and 9 (foreign revisions before and between the seeds): the
//     two histories are the same up to the renumbering, and RealCheck agrees on them.

import (
	"bufio"
	"context"
	"fmt"
	"os"
	"os/exec"
	"strconv"
	"strings"
	"sync/atomic"
	"testing"
	"time"

	"github.com/anishathalye/porcupine"
	"go.uber.org/zap"

	clientv3 "go.etcd.io/etcd/client/v3"
	"go.etcd.io/etcd/client/v3/kubernetes"
	"k8s.io/apiserver/pkg/storage"

	"github.com/mit-pdos/etcd-grove/examples/lib/etcdstart"
	"github.com/mit-pdos/etcd-grove/examples/lib/lintest"
	"github.com/mit-pdos/etcd-grove/examples/lib/walarea"

	k8s "github.com/mit-pdos/etcd-grove/examples/k8s/etcd3"
)

// The members the risk tests start: name, peer and client port (none another test's).
type riskMember struct {
	name         string
	peer, client int
}

var (
	riskCP = riskMember{"k8srisk-cp", 24811, 24812}
	riskFH = riskMember{"k8srisk-fh", 24813, 24814}
	riskSA = riskMember{"k8srisk-sa", 24815, 24816}
	riskSB = riskMember{"k8srisk-sb", 24817, 24818}
)

// riskIter counts a test's runs in this process (-count), for TestForeignHeavy's modes.
var riskIter = map[string]int{}

// riskChild runs body in a child process (K8SRISK_CHILD set) with mode in K8SRISK_MODE, and, in
// the parent, removes the members' files after it and fails if the child failed, logging the
// child's "risk:" lines and failures.
func riskChild(t *testing.T, test string, mode string, ms []riskMember, body func(t *testing.T, mode string)) {
	if os.Getenv("K8SRISK_CHILD") != "" {
		for _, m := range ms {
			walarea.Reset(t, m.name)
		}
		body(t, os.Getenv("K8SRISK_MODE"))
		return
	}
	defer func() {
		for _, m := range ms {
			os.RemoveAll(walarea.DataDir(m.name))
			os.RemoveAll(walarea.Area(m.name))
		}
	}()
	cmd := exec.Command(os.Args[0], "-test.run", "^"+test+"$", "-test.v", "-test.count=1")
	cmd.Env = append(os.Environ(), "K8SRISK_CHILD=1", "K8SRISK_MODE="+mode)
	out, err := cmd.CombinedOutput()
	sc := bufio.NewScanner(strings.NewReader(string(out)))
	sc.Buffer(make([]byte, 1<<20), 1<<24)
	for sc.Scan() {
		l := sc.Text()
		if strings.Contains(l, "risk:") || strings.Contains(l, "panic") || strings.Contains(l, "FAIL") ||
			strings.Contains(l, "Error") {
			t.Log(strings.TrimSpace(l))
		}
	}
	if err != nil {
		t.Fatalf("%s (%s): child failed: %v", test, mode, err)
	}
}

// startRisk starts the member m (one member of a new cluster), serves its client port and connects
// a kubernetes client (one attempt per call, as Main's) and a plain client to it.
func startRisk(t *testing.T, m riskMember) (*kubernetes.Client, *clientv3.Client) {
	lg := zap.NewNop()
	caddr := "127.0.0.1:" + strconv.Itoa(m.client)
	srv, err := etcdstart.StartServer(m.name, "127.0.0.1:"+strconv.Itoa(m.peer), caddr, lg)
	if err != nil {
		t.Fatal(err)
	}
	if err := etcdstart.Serve(srv, caddr); err != nil {
		t.Fatal(err)
	}
	kc, err := kubernetes.New(clientv3.Config{Endpoints: []string{caddr}, Logger: lg, MaxUnaryRetries: 1})
	if err != nil {
		t.Fatal(err)
	}
	cli, err := etcdstart.NewClient(caddr, lg)
	if err != nil {
		t.Fatal(err)
	}
	return kc, cli
}

// newRiskStore seeds the member's cluster (SeedShared) and makes the store over kc.
func newRiskStore(t *testing.T, kc *kubernetes.Client, cli *clientv3.Client) (k8s.Seeded, storage.Interface) {
	if !k8s.SetFeatures() {
		t.Fatal("the features could not be set")
	}
	seeded, ok := k8s.SeedShared(cli)
	if !ok {
		t.Fatal("the seeds failed")
	}
	s, ok := k8s.NewStoreOnly(kc)
	if !ok {
		t.Fatal("NewStoreOnly failed")
	}
	return seeded, s
}

func curRev(cli *clientv3.Client) (int64, bool) {
	resp, err := cli.Get(context.Background(), "/k8sdist-compactor/probe")
	if err != nil {
		return 0, false
	}
	return resp.Header.Revision, true
}

var kindName = []string{"create", "delete", "update", "get", "list", "watch"}

func kname(k int) string {
	if k >= 0 && k < len(kindName) {
		return kindName[k]
	}
	return "kind" + strconv.Itoa(k)
}

// TestCompactedProvenance: risk 1.
func TestCompactedProvenance(t *testing.T) {
	riskChild(t, "TestCompactedProvenance", "", []riskMember{riskCP}, func(t *testing.T, _ string) {
		kc, cli := startRisk(t, riskCP)
		seeded, s := newRiskStore(t, kc, cli)
		const clients, ops, watchers, wops = 4, 400, 2, 40
		tbl := seeded.NewCache(clients, ops)
		var compactions, past, pinned, bad atomic.Int64
		var byKind [8]atomic.Int64
		stop := make(chan struct{})
		done := make(chan struct{})
		go func() {
			defer close(done)
			for {
				select {
				case <-stop:
					return
				default:
				}
				if r, ok := curRev(cli); ok {
					if _, err := cli.Compact(context.Background(), r); err == nil {
						compactions.Add(1)
					}
				}
				time.Sleep(time.Millisecond)
			}
		}()
		apply := func(input any) any {
			in := input.(k8s.Input)
			out := k8s.Serve(s, in)
			if compacted(out.Raw) {
				if in.Kind >= 0 && in.Kind < len(byKind) {
					byKind[in.Kind].Add(1)
				}
				switch {
				case k8s.PastRead(in):
					past.Add(1)
				case k8s.PinnedRead(in):
					pinned.Add(1)
				default:
					bad.Add(1)
					t.Errorf("risk: a compacted answer at no old revision: %s, MinRV %q, match %d, limit %d, "+
						"send-initial %d, use-cached %v, err %v", kname(in.Kind), in.MinRV, in.Match, in.Limit,
						in.SendInit, in.UseCached, out.Raw.Err)
				}
			}
			k8s.Record(tbl, in, out)
			return out
		}
		gen := func(id int) any { return k8s.Gen(tbl, id) }
		_, lops := lintest.RunLin2(k8s.AcceptAll(), apply, gen, lintest.CounterClock(), clients, ops,
			watchers, wops, CheckTimeout)
		close(stop)
		<-done
		ks := ""
		for k := range byKind {
			if n := byKind[k].Load(); n > 0 {
				ks += fmt.Sprintf(" %s=%d", kname(k), n)
			}
		}
		t.Logf("risk: %d operations, %d compactions; compacted answers: %d past, %d pinned, %d at no old "+
			"revision; by kind:%s", len(lops), compactions.Load(), past.Load(), pinned.Load(), bad.Load(), ks)
	})
}

// TestForeignHeavy: risk 2. Its runs cycle through the writer's modes: "throughout" (from the
// seeds on), "tail" (from the last unary operation's answer on) and "none" (no foreign writer: how
// often NoForeign holds at all).
func TestForeignHeavy(t *testing.T) {
	mode := []string{"throughout", "tail", "none"}[riskIter["fh"]%3]
	riskIter["fh"]++
	riskChild(t, "TestForeignHeavy", mode, []riskMember{riskFH}, func(t *testing.T, mode string) {
		kc, cli := startRisk(t, riskFH)
		seeded, s := newRiskStore(t, kc, cli)
		const clients, ops, watchers, wops = 4, 100, 2, 10
		tbl := seeded.NewCache(clients, ops)
		var applied, unary, foreign atomic.Int64
		stop := make(chan struct{})
		done := make(chan struct{})
		go func() {
			defer close(done)
			for {
				select {
				case <-stop:
					return
				default:
				}
				if mode == "none" || mode == "tail" && unary.Load() < clients*ops {
					time.Sleep(100 * time.Microsecond)
					continue
				}
				if foreign.Load() >= 10*applied.Load() {
					time.Sleep(100 * time.Microsecond)
					continue
				}
				n := foreign.Add(1)
				if _, err := cli.Put(context.Background(), "/k8sdist-compactor/w", strconv.FormatInt(n, 10)); err != nil {
					foreign.Add(-1)
				}
			}
		}()
		apply := func(input any) any {
			in := input.(k8s.Input)
			out := k8s.Serve(s, in)
			k8s.Record(tbl, in, out)
			applied.Add(1)
			if in.Kind != k8s.KWatch {
				unary.Add(1)
			}
			return out
		}
		gen := func(id int) any { return k8s.Gen(tbl, id) }
		_, lops := lintest.RunLin2(k8s.AcceptAll(), apply, gen, lintest.CounterClock(), clients, ops,
			watchers, wops, CheckTimeout)
		close(stop)
		<-done
		r, m := CheckShared(seeded, k8s.HistoryRevs(lops), lops, CheckTimeout)
		if r == porcupine.Illegal {
			dumpRisk(t, seeded, lops)
			t.Errorf("risk: CheckShared Illegal (mode %s)", mode)
		}
		ff, nf := k8s.FailureFree(lops), seeded.NoForeign(lops)
		real := "skipped"
		if ff && nf {
			rr := seeded.RealCheck(lops, CheckTimeout)
			real = fmt.Sprint(rr)
			if rr == porcupine.Illegal {
				dumpRisk(t, seeded, lops)
				t.Errorf("risk: NoForeign holds and RealCheck is Illegal (mode %s)", mode)
			}
		}
		t.Logf("risk: mode %s: %d operations, %d foreign revisions; CheckShared %v (model %d); "+
			"failure-free %v, NoForeign %v, RealCheck %s", mode, len(lops), foreign.Load(), r, m, ff, nf, real)
	})
}

// dumpRisk writes the history (dumpHistory's format) to $K8SRISK_DUMP.<pid>, if set.
func dumpRisk(t *testing.T, seeded k8s.Seeded, ops []porcupine.Operation) {
	if p := os.Getenv("K8SRISK_DUMP"); p != "" {
		t.Setenv("DIST_DUMP", p)
		dumpHistory(seeded, ops)
		t.Logf("risk: history dumped to %s.%d", p, os.Getpid())
	}
}

// shiftRV renumbers a revision of the cluster seeded at 2 and 3 to the one seeded at 5 and 9.
func shiftRV(r uint64) uint64 {
	switch {
	case r <= 1:
		return r
	case r == 2:
		return 5
	case r == 3:
		return 9
	}
	return r + 6
}

// shiftBytes renumbers a resource version in the driver's 8-byte encoding (any other string, the
// empty one included, is kept).
func shiftBytes(s string) string {
	if len(s) != 8 {
		return s
	}
	var n uint64
	for i := 0; i < 8; i++ {
		n = n<<8 | uint64(s[i])
	}
	return k8s.RVBytes(shiftRV(n))
}

func shiftInput(in k8s.Input) k8s.Input {
	in.MinRV = shiftBytes(in.MinRV)
	in.PreRV = shiftBytes(in.PreRV)
	if in.Cached.ResourceVersion != 0 {
		in.Cached.ResourceVersion = shiftRV(in.Cached.ResourceVersion)
	}
	return in
}

// sameShifted says whether the unary output b is a up to the renumbering, on the fields the
// driver's model reads but the encoded items.
func sameShifted(a, b k8s.Output) bool {
	sh := func(r uint64) uint64 {
		if r == 0 {
			return 0
		}
		return shiftRV(r)
	}
	errRV := a.ErrRV
	if errRV > 0 {
		errRV = int64(shiftRV(uint64(errRV)))
	}
	return a.Err == b.Err && errRV == b.ErrRV && a.Name == b.Name && a.Namespace == b.Namespace &&
		a.UID == b.UID && a.Value == b.Value && a.Node == b.Node && a.App == b.App &&
		sh(a.RV) == b.RV && sh(a.ListRV) == b.ListRV && a.HasRemaining == b.HasRemaining &&
		a.Remaining == b.Remaining && (a.Continue == "") == (b.Continue == "")
}

// TestRealCheckShifted: risk 3.
func TestRealCheckShifted(t *testing.T) {
	riskChild(t, "TestRealCheckShifted", "", []riskMember{riskSA, riskSB}, func(t *testing.T, _ string) {
		kcA, cliA := startRisk(t, riskSA)
		kcB, cliB := startRisk(t, riskSB)
		seededA, sA := newRiskStore(t, kcA, cliA)
		if r1, r2 := seededA.SeedRevs(); r1 != 2 || r2 != 3 {
			t.Fatalf("seeds at %d, %d, want 2, 3", r1, r2)
		}
		// cluster B: the seeds' stored bytes (SeedShared's, read off A) at 5 and 9, foreign
		// revisions at 2-4 and 6-8
		ctx := context.Background()
		put := func(k, v string, want int64) {
			resp, err := cliB.Put(ctx, k, v)
			if err != nil || resp.Header.Revision != want {
				t.Fatalf("put %s: %v (revision %v, want %d)", k, err, resp, want)
			}
		}
		rev := int64(2)
		for _, k := range []string{"ns-1/pod-1", "ns-2/pod-2"} {
			for i := 0; i < 3; i++ {
				put("/k8sdist-compactor/w", "f", rev)
				rev++
			}
			g, err := cliA.Get(ctx, k8s.Prefix+"/objs/"+k)
			if err != nil || len(g.Kvs) != 1 {
				t.Fatalf("get %s: %v", k, err)
			}
			put(k8s.Prefix+"/objs/"+k, string(g.Kvs[0].Value), rev)
			rev++
		}
		seededB := k8s.SeededAt(5, 9)
		sB, ok := k8s.NewStoreOnly(kcB)
		if !ok {
			t.Fatal("NewStoreOnly B failed")
		}
		const clients, ops, watchers = 3, 120, 1
		tbl := seededA.NewCache(clients, ops)
		var hA, hB []porcupine.Operation
		diff, watchDiff := 0, 0
		step := func(id int) {
			in := k8s.Gen(tbl, id)
			outA := k8s.Serve(sA, in)
			inB := shiftInput(in)
			outB := k8s.Serve(sB, inB)
			k8s.Record(tbl, in, outA)
			if in.Kind == k8s.KWatch {
				if len(outA.Raw.Events) != len(outB.Raw.Events) || outA.WFailed != outB.WFailed {
					watchDiff++
				}
			} else if !sameShifted(outA, outB) {
				diff++
				if diff <= 5 {
					t.Logf("risk: %s differs: A %+v / B %+v", kname(in.Kind), outA, outB)
				}
			}
			c := int64(2 * len(hA))
			hA = append(hA, porcupine.Operation{ClientId: id, Input: in, Output: outA, Call: c, Return: c + 1})
			hB = append(hB, porcupine.Operation{ClientId: id, Input: inB, Output: outB, Call: c, Return: c + 1})
		}
		for i := 0; i < clients*ops; i++ {
			step(i % clients)
			if i%10 == 9 {
				step(clients + (i/10)%watchers)
			}
		}
		if diff > 0 {
			t.Errorf("risk: %d unary answers differ beyond the renumbering", diff)
		}
		ffA, ffB := k8s.FailureFree(hA), k8s.FailureFree(hB)
		nfA, nfB := seededA.NoForeign(hA), seededB.NoForeign(hB)
		rA := seededA.RealCheck(hA, CheckTimeout)
		rB := seededB.RealCheck(hB, CheckTimeout)
		if rA != rB || (ffA && ffB && rA != porcupine.Ok) {
			t.Errorf("risk: RealCheck disagrees or rejects: seeds 2,3 %v, seeds 5,9 %v", rA, rB)
		}
		// non-vacuity: the seeds matter
		xAB := seededA.RealCheck(hB, CheckTimeout)
		xBA := seededB.RealCheck(hA, CheckTimeout)
		if xAB == porcupine.Ok || xBA == porcupine.Ok {
			t.Errorf("risk: a history passed RealCheck from the other seeds: %v, %v", xAB, xBA)
		}
		cB, _ := CheckShared(seededB, k8s.HistoryRevs(hB), hB, CheckTimeout)
		if cB != porcupine.Ok {
			t.Errorf("risk: CheckShared of the shifted history: %v", cB)
		}
		t.Logf("risk: %d operations; failure-free %v/%v, NoForeign %v/%v; RealCheck %v/%v; crossed %v/%v; "+
			"CheckShared(5,9) %v; watch answers differing in length %d", len(hA), ffA, ffB, nfA, nfB, rA, rB,
			xAB, xBA, cB, watchDiff)
	})
}
