package etcd3

import (
	"context"
	"fmt"
	"math/rand"
	"os"
	"strconv"
	"sync"
	"sync/atomic"
	"testing"
	"time"

	"github.com/anishathalye/porcupine"
	clientv3 "go.etcd.io/etcd/client/v3"
	"go.etcd.io/etcd/client/v3/kubernetes"
	"go.uber.org/zap"
	"k8s.io/apimachinery/pkg/watch"
	"k8s.io/apiserver/pkg/features"
	"k8s.io/apiserver/pkg/storage"
	utilfeature "k8s.io/apiserver/pkg/util/feature"

	"github.com/mit-pdos/etcd-grove/examples/lib/cluster3"
	"github.com/mit-pdos/etcd-grove/examples/lib/etcdstart"
	"github.com/mit-pdos/etcd-grove/examples/lib/lintest"
)

// The watch traffic's tests (stage 7f-0/7f-6, notes/k8s-7f6-scope.md): the check on hand-made
// histories, the generator's cases and the requests the proof assumes (WatchInOk), real runs on one
// member, a cluster and a partitioned cluster with the counts of what the watches reached,
// corrupted watches (porcupine must answer Illegal), and the driver's own cancellation of a watch.

// watchStats counts a run's watches: by behaviour, request mode and outcome; their events by type;
// the watch-lists that reached their initial-events-end bookmark and those that ended before it;
// the watches with a progress bookmark, with an Error event, with events after an Error event.
type watchStats struct {
	mu                                   sync.Mutex
	watches, failed, skipped, withEvents int
	initial, initEnd, initCut            int
	progress, withErr, afterErr          int
	pinned                               int
	byType                               [6]int
	byBeh                                [4]int
	bySendInit                           [3]int
	byScope                              [3]int
	maxRev                               uint64
	unaryFails                           atomic.Int64
	unary                                atomic.Int64
}

// scopeOf is a watch's scope: 0 the cluster, 1 a namespace, 2 an object.
func scopeOf(in Input) int {
	if in.WKey == ResourcePrefix+"/" {
		return 0
	}
	if len(in.WKey) > len(ResourcePrefix)+1 && !containsSlash(in.WKey[len(ResourcePrefix)+1:]) {
		return 1
	}
	return 2
}

func containsSlash(s string) bool {
	for i := 0; i < len(s); i++ {
		if s[i] == '/' {
			return true
		}
	}
	return false
}

func (ws *watchStats) hook(in Input, out Output) Output {
	if in.Kind != KWatch {
		ws.unary.Add(1)
		if out.Err == EOther {
			ws.unaryFails.Add(1)
		}
		return out
	}
	ws.mu.Lock()
	defer ws.mu.Unlock()
	if in.Skip {
		ws.skipped++
		return out
	}
	ws.watches++
	ws.byBeh[in.Behavior]++
	ws.bySendInit[in.SendInit]++
	ws.byScope[scopeOf(in)]++
	if out.WFailed {
		ws.failed++
		return out
	}
	evs, _ := decodeWEvents(out.WEvents)
	if len(evs) > 0 {
		ws.withEvents++
	}
	if req, _ := parseRV(in.MinRV); req > 0 && len(evs) > 0 {
		ws.pinned++
	}
	errAt, bm, prog := -1, false, false
	for i, ev := range evs {
		ws.byType[ev.Type]++
		if ev.Type == WError && errAt < 0 {
			errAt = i
		}
		if ev.Type == WBookmark {
			if ev.Obj.Annotated {
				bm = true
			} else {
				prog = true
			}
		}
		if ev.Obj.ResourceVersion > ws.maxRev {
			ws.maxRev = ev.Obj.ResourceVersion
		}
	}
	if in.SendInit == 2 && len(evs) > 0 {
		ws.initial++
		if bm {
			ws.initEnd++
		} else {
			ws.initCut++
		}
	}
	if prog {
		ws.progress++
	}
	if errAt >= 0 {
		ws.withErr++
		if errAt != len(evs)-1 {
			ws.afterErr++
		}
	}
	return out
}

func (ws *watchStats) log(t *testing.T) {
	ws.mu.Lock()
	defer ws.mu.Unlock()
	t.Logf("watches %d (fast/slow/hiccup/stalled %v; SendInitialEvents nil/false/true %v; "+
		"cluster/namespace/object %v), failed %d, skipped %d, with events %d, pinned (RV > 0) with "+
		"events %d, watch-lists with events %d (bookmark reached %d, ended before it %d), with a "+
		"progress bookmark %d, with an error %d, events after an error %d; events "+
		"added/modified/deleted/bookmark/error/bad %v; max revision %d; unary calls %d (failed %d)",
		ws.watches, ws.byBeh, ws.bySendInit, ws.byScope, ws.failed, ws.skipped, ws.withEvents,
		ws.pinned, ws.initial, ws.initEnd, ws.initCut, ws.progress, ws.withErr, ws.afterErr,
		ws.byType, ws.maxRev, ws.unary.Load(), ws.unaryFails.Load())
}

// peakRSS is the process's peak resident set (VmHWM), for the memory reports.
func peakRSS() string {
	b, err := os.ReadFile("/proc/self/status")
	if err != nil {
		return "?"
	}
	s := string(b)
	for len(s) > 0 {
		i := 0
		for i < len(s) && s[i] != '\n' {
			i++
		}
		if l := s[:i]; len(l) > 6 && l[:6] == "VmHWM:" {
			return l[6:]
		}
		if i == len(s) {
			break
		}
		s = s[i+1:]
	}
	return "?"
}

// checkWWith is Check (the same cache and RunLin2 call) with every output passed through hook
// before it is recorded (the tests' counts and corruptions).
func checkWWith(s storage.Interface, st0 mstore, h0 []mstore, clients, ops, watchers, wops int,
	hook func(Input, Output) Output) porcupine.CheckResult {
	tbl := newWCache(clients, int64(clients)*int64(ops), st0.rv)
	apply := func(input any) any {
		out := Apply(s, tbl, input).(Output)
		if hook != nil {
			out = hook(input.(Input), out)
		}
		return out
	}
	gen := func(id int) any { return Gen(tbl, id) }
	r, _ := lintest.RunLin2(Model(st0, h0), apply, gen, lintest.CounterClock(), clients, ops,
		watchers, wops, 0)
	return r
}

// decodeMode sets the ConcurrentWatchObjectDecode feature as K8SETCD3_DECODE says ("serial": off,
// "concurrent": on; the binary's default otherwise) and returns its value: the theorems cover both
// (Q7f-3), so the runs exercise both branches of the watcher's processEvents.
func decodeMode(t *testing.T) bool {
	switch os.Getenv("K8SETCD3_DECODE") {
	case "serial":
		if err := utilfeature.DefaultMutableFeatureGate.Set("ConcurrentWatchObjectDecode=false"); err != nil {
			t.Fatal(err)
		}
	case "concurrent":
		if err := utilfeature.DefaultMutableFeatureGate.Set("ConcurrentWatchObjectDecode=true"); err != nil {
			t.Fatal(err)
		}
	}
	on := utilfeature.DefaultFeatureGate.Enabled(features.ConcurrentWatchObjectDecode)
	t.Logf("ConcurrentWatchObjectDecode %v", on)
	return on
}

// singleWAt is Main's setup (one member, one attempt per call) and checkWWith, on a member of its
// own for attempt a (its name and addresses), so that a process can run several.
func singleWAt(t *testing.T, a int, clients, ops, watchers, wops int, hook func(Input, Output) Output) porcupine.CheckResult {
	lg := zap.NewNop()
	name, peer, cl := "k8setcd3", "127.0.0.1:23906", clientAddr
	if a > 0 {
		name = fmt.Sprintf("k8setcd3w%d", a)
		peer = fmt.Sprintf("127.0.0.1:%d", 23970+a)
		cl = fmt.Sprintf("127.0.0.1:%d", 23980+a)
	}
	srv, err := etcdstart.StartServer(name, peer, cl, lg)
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
	decodeMode(t)
	s, st0, h0, ok := newStore(kc)
	if !ok {
		t.Fatal("store")
	}
	return checkWWith(s, st0, h0, clients, ops, watchers, wops, hook)
}

// wantReached fails the test unless every count named is positive.
func wantReached(t *testing.T, counts map[string]int) {
	for name, n := range counts {
		if n == 0 {
			t.Errorf("the watch traffic did not reach: %s", name)
		}
	}
}

// TestWatchOkEdges checks watchOk on hand-made histories: a bookmark past the configuration and a
// bad event are rejected; a dropped middle event is rejected; a dropped first event of an unpinned
// watch is accepted (what no check can see); the encoding round-trips.
func TestWatchOkEdges(t *testing.T) {
	o := func(v string, rv uint64) Obj {
		return Obj{Namespace: "ns-1", Name: "pod-1", Value: v, ResourceVersion: rv}
	}
	// revisions 1 (empty), 2 (created x), 3 (y), 4 (z), 5 (w)
	h := []mstore{{rv: 1}, {items: []item{{key: "ns-1/pod-1", obj: o("x", 2), canon: true}}, rv: 2},
		{items: []item{{key: "ns-1/pod-1", obj: o("y", 3), canon: true}}, rv: 3},
		{items: []item{{key: "ns-1/pod-1", obj: o("z", 4), canon: true}}, rv: 4},
		{items: []item{{key: "ns-1/pod-1", obj: o("w", 5), canon: true}}, rv: 5}}
	c := mcfg{st: h[4], hist: histOf(h)}
	in := Input{Kind: KWatch, WKey: ResourcePrefix + "/", Recursive: true, SendInit: 1, Match: MNotOlderThan}
	pinned := Input{Kind: KWatch, WKey: ResourcePrefix + "/", Recursive: true, MinRV: rvString(2)}
	wl := Input{Kind: KWatch, WKey: ResourcePrefix + "/", Recursive: true, SendInit: 2, Bookmarks: true,
		Match: MNotOlderThan, MinRV: rvString(3)}
	ev := func(t int, v string, rv uint64) WEvent { return WEvent{Type: t, Obj: o(v, rv)} }
	bmk := func(rv uint64, ann bool) WEvent {
		return WEvent{Type: WBookmark, Obj: Obj{ResourceVersion: rv, Annotated: ann}}
	}
	cases := []struct {
		name string
		in   Input
		evs  []WEvent
		want bool
	}{
		{"full", in, []WEvent{ev(WModified, "y", 3), ev(WModified, "z", 4), ev(WModified, "w", 5)}, true},
		{"middle dropped", in, []WEvent{ev(WModified, "y", 3), ev(WModified, "w", 5)}, false},
		{"first dropped (invisible)", in, []WEvent{ev(WModified, "z", 4), ev(WModified, "w", 5)}, true},
		{"bookmark past", in, []WEvent{ev(WModified, "w", 5), bmk(6, false)}, false},
		{"bookmark at", in, []WEvent{ev(WModified, "w", 5), bmk(5, false)}, true},
		{"bad", in, []WEvent{ev(WModified, "w", 5), {Type: WBad}}, false},
		{"error then event", in, []WEvent{ev(WModified, "z", 4), {Type: WError}, ev(WModified, "w", 5)}, true},
		{"no events", in, nil, true},
		{"pinned full", pinned, []WEvent{ev(WModified, "y", 3), ev(WModified, "z", 4)}, true},
		{"pinned first dropped", pinned, []WEvent{ev(WModified, "z", 4)}, false},
		{"watch-list", wl, []WEvent{ev(WAdded, "z", 4), bmk(4, true), ev(WModified, "w", 5)}, true},
		{"watch-list initial at 3", wl, []WEvent{ev(WAdded, "y", 3), bmk(3, true), ev(WModified, "z", 4)}, true},
		{"watch-list stale initial", wl, []WEvent{ev(WAdded, "y", 3), bmk(4, true)}, false},
		{"watch-list before bookmark", wl, []WEvent{ev(WAdded, "w", 5)}, true},
		{"watch-list before bookmark, too old", wl, []WEvent{ev(WAdded, "x", 2)}, false},
		{"watch-list unannotated", wl, []WEvent{ev(WAdded, "z", 4), bmk(4, false)}, false},
		{"watch-list gap", wl, []WEvent{ev(WAdded, "y", 3), bmk(3, true), ev(WModified, "w", 5)}, false},
	}
	for _, tc := range cases {
		got := watchOk(tc.in, Output{WEvents: encodeWEvents(tc.evs)}, c)
		if got != tc.want {
			t.Errorf("%s: watchOk = %v, want %v", tc.name, got, tc.want)
		}
	}
	if !watchOk(in, Output{WFailed: true}, c) || !watchOk(Input{Kind: KWatch, Skip: true}, Output{}, c) {
		t.Errorf("a failed or skipped watch must constrain nothing")
	}
	if watchOk(in, Output{WEvents: "x"}, c) {
		t.Errorf("an output that does not decode must be rejected")
	}
	evs := []WEvent{ev(WAdded, "x", 2), bmk(2, true), {Type: WError}}
	back, ok := decodeWEvents(encodeWEvents(evs))
	if !ok || len(back) != len(evs) {
		t.Fatalf("decodeWEvents: %v %v", back, ok)
	}
	for i := range evs {
		if back[i] != evs[i] {
			t.Errorf("round trip %d: %+v != %+v", i, back[i], evs[i])
		}
	}
}

// watchInOk is KWatchStream.lean's WatchInOk, the requests the proof assumes the generator makes:
// a watch-list asks for NotOlderThan; RV 0 without a watch-list asks for SendInitialEvents = false
// and NotOlderThan; any other RV the legacy match.
func watchInOk(in Input) bool {
	req, err := parseRV(in.MinRV)
	if err != nil {
		return false
	}
	if in.SendInit == 2 {
		return in.Match == MNotOlderThan
	}
	return (req == 0 && in.Match == MNotOlderThan && in.SendInit == 1) || (req > 0 && in.Match == MLegacy && in.SendInit == 0)
}

// TestGenWatchCases draws genWatchFrom on random numbers, with and without a cached object: every
// request satisfies watchInOk, is a watch, and the draws reach every case of the generator (the
// test's randomWatchRequest).
func TestGenWatchCases(t *testing.T) {
	rng := rand.New(rand.NewSource(1))
	counts := map[string]int{}
	cached := Obj{Namespace: "ns-1", Name: "pod-1", ResourceVersion: 300}
	for i := 0; i < 20000; i++ {
		hasC := i%2 == 0
		in := genWatchFrom(rng.Uint64(), 7, cached, hasC, 0)
		if in.Kind != KWatch || in.Client != 7 || in.Skip {
			t.Fatalf("not a watch of client 7: %+v", in)
		}
		if !watchInOk(in) {
			t.Fatalf("watchInOk fails: %+v", in)
		}
		req, _ := parseRV(in.MinRV)
		counts["SendInit="+strconv.Itoa(in.SendInit)]++
		counts["behavior="+strconv.Itoa(in.Behavior)]++
		counts["scope="+strconv.Itoa(scopeOf(in))]++
		counts["field="+strconv.Itoa(in.Field)]++
		counts["recursive="+strconv.FormatBool(in.Recursive)]++
		counts["bookmarks="+strconv.FormatBool(in.Bookmarks)]++
		counts["app="+strconv.FormatBool(in.SelApp != "")]++
		counts["missing ns="+strconv.FormatBool(in.SelNS == "ns-nonexistent")]++
		counts["missing name="+strconv.FormatBool(in.SelName == "pod-nonexistent")]++
		switch {
		case in.MinRV == "":
			counts["rv empty"]++
		case req == 0:
			counts["rv 0"]++
		case req == 1:
			counts["rv 1"]++
		case req == 300:
			counts["rv cached"]++
		case req < 300:
			counts["rv past"]++
		default:
			counts["rv future"]++
		}
		if !hasC && req > 1 {
			t.Fatalf("a relative RV with no cached object: %+v", in)
		}
		if in.SendInit == 2 && req > 300 {
			t.Fatalf("a watch-list from the future: %+v", in)
		}
	}
	want := []string{"SendInit=0", "SendInit=1", "SendInit=2", "rv empty", "rv 0", "rv 1",
		"rv cached", "rv past", "rv future", "recursive=true", "recursive=false",
		"bookmarks=true", "bookmarks=false", "app=true", "app=false", "missing ns=true",
		"missing name=true"}
	for i := 0; i < 4; i++ {
		want = append(want, "behavior="+strconv.Itoa(i))
	}
	for i := 0; i < 3; i++ {
		want = append(want, "scope="+strconv.Itoa(i))
	}
	for i := 0; i <= FCombined; i++ {
		want = append(want, "field="+strconv.Itoa(i))
	}
	m := map[string]int{}
	for _, w := range want {
		m[w] = counts[w]
	}
	wantReached(t, m)
	t.Logf("%v", counts)
}

// cancelStore is a store whose Watch records the context and the watch it returns.
type cancelStore struct {
	storage.Interface
	mu   sync.Mutex
	ctxs []context.Context
	ws   []watch.Interface
}

func (c *cancelStore) Watch(ctx context.Context, key string, opts storage.ListOptions) (watch.Interface, error) {
	w, err := c.Interface.Watch(ctx, key, opts)
	if err == nil {
		c.mu.Lock()
		c.ctxs = append(c.ctxs, ctx)
		c.ws = append(c.ws, w)
		c.mu.Unlock()
	}
	return w, err
}

// TestWatchCancel checks the driver's own cancellation (WithCancel(Background()), in place of the
// test's WithTimeout): once watchEvents returns, its context is canceled and the watch's result
// channel closes (the watcher's goroutines end), for every behaviour, while writes go on; and a
// watch still ends at watchDuration.
func TestWatchCancel(t *testing.T) {
	inChild(t, "TestWatchCancel", "", func(t *testing.T) {
		lg := zap.NewNop()
		srv, err := etcdstart.StartServer("k8setcd3", "127.0.0.1:23906", clientAddr, lg)
		if err != nil {
			t.Fatal(err)
		}
		if err := etcdstart.Serve(srv, clientAddr); err != nil {
			t.Fatal(err)
		}
		kc, err := kubernetes.New(clientv3.Config{Endpoints: []string{clientAddr}, Logger: lg, MaxUnaryRetries: 1})
		if err != nil {
			t.Fatal(err)
		}
		s0, _, _, ok := newStore(kc)
		if !ok {
			t.Fatal("store")
		}
		cs := &cancelStore{Interface: s0}
		stop := make(chan struct{})
		go func() {
			for i := 0; ; i++ {
				select {
				case <-stop:
					return
				case <-time.After(5 * time.Millisecond):
				}
				in := Input{Kind: KUpdate, Key: "ns-1/pod-1", Val: "v" + strconv.Itoa(i)}
				call(s0, in)
			}
		}()
		defer close(stop)
		rng := rand.New(rand.NewSource(2))
		for i := 0; i < 24; i++ {
			in := genWatchFrom(rng.Uint64(), 0, Obj{}, false, 0)
			in.Behavior = i % 4
			start := time.Now()
			_, _, failed := watchEvents(cs, in)
			d := time.Since(start)
			if failed {
				t.Fatalf("watch %d: the Watch call failed", i)
			}
			if d > watchDuration+hiccupDuration+500*time.Millisecond {
				t.Errorf("watch %d (behavior %d) took %v", i, in.Behavior, d)
			}
			cs.mu.Lock()
			ctx, w := cs.ctxs[len(cs.ctxs)-1], cs.ws[len(cs.ws)-1]
			cs.mu.Unlock()
			if ctx.Err() != context.Canceled {
				t.Fatalf("watch %d: context not canceled after watchEvents: %v", i, ctx.Err())
			}
			closed := false
			deadline := time.After(5 * time.Second)
			for !closed {
				select {
				case _, open := <-w.ResultChan():
					closed = !open
				case <-deadline:
					t.Fatalf("watch %d: result channel still open 5s after watchEvents", i)
				}
			}
		}
	})
}

// TestMainWatch runs the driver with watchers on one member (Main's setup), in a process of its
// own: Ok, and the watch traffic reaches its cases (a mode-count test, as TestTrafficReachesCases
// is for the unary traffic).
func TestMainWatch(t *testing.T) {
	inChild(t, "TestMainWatch", "", func(t *testing.T) {
		ws := &watchStats{}
		start := time.Now()
		r := singleWAt(t, 0, 8, 300, 16, 8, ws.hook)
		ws.log(t)
		t.Logf("%v in %v, peak RSS %s", r, time.Since(start), peakRSS())
		if r != porcupine.Ok {
			t.Fatalf("got %v, want Ok", r)
		}
		ws.mu.Lock()
		defer ws.mu.Unlock()
		wantReached(t, map[string]int{
			"fast": ws.byBeh[BFast], "slow": ws.byBeh[BSlow], "hiccup": ws.byBeh[BHiccup],
			"stalled": ws.byBeh[BStalled], "SendInitialEvents nil": ws.bySendInit[0],
			"SendInitialEvents false": ws.bySendInit[1], "SendInitialEvents true": ws.bySendInit[2],
			"cluster scope": ws.byScope[0], "namespace scope": ws.byScope[1],
			"object scope": ws.byScope[2], "watches with events": ws.withEvents,
			"pinned watches with events": ws.pinned, "watch-lists with events": ws.initial,
			"initial-events-end bookmarks": ws.initEnd, "added": ws.byType[WAdded],
			"modified": ws.byType[WModified], "deleted": ws.byType[WDeleted],
			"bookmarks": ws.byType[WBookmark],
		})
		// (skipped watches depend on timing: under load the watchers can run all their watches
		// before the unary traffic ends; the cluster runs reach them, §8 of the Scope)
		if ws.byType[WBad] != 0 {
			t.Errorf("%d bad events", ws.byType[WBad])
		}
	})
}

// corruptions are the ways TestWatchCorrupt corrupts a watch: the first change event's object's
// value, resource version or type, or that event duplicated; a middle change event dropped (one
// the check can see: an unpinned window's ends are its first and last events); and none (the run
// must then be Ok).
var corruptions = map[string]func(evs []WEvent, cs []int) ([]WEvent, bool){
	"none": func(evs []WEvent, cs []int) ([]WEvent, bool) { return evs, true },
	"value": func(evs []WEvent, cs []int) ([]WEvent, bool) {
		evs[cs[0]].Obj.Value += "!"
		return evs, true
	},
	"rv": func(evs []WEvent, cs []int) ([]WEvent, bool) {
		evs[cs[0]].Obj.ResourceVersion++
		return evs, true
	},
	"type": func(evs []WEvent, cs []int) ([]WEvent, bool) {
		evs[cs[0]].Type = (evs[cs[0]].Type + 1) % 3
		return evs, true
	},
	"dup": func(evs []WEvent, cs []int) ([]WEvent, bool) {
		i := cs[0]
		out := append(evs[:i+1:i+1], evs[i])
		return append(out, evs[i+1:]...), true
	},
	"drop": func(evs []WEvent, cs []int) ([]WEvent, bool) {
		if len(cs) < 3 {
			return evs, false
		}
		i := cs[1]
		return append(evs[:i:i], evs[i+1:]...), true
	},
}

// changeEvents are the indices of a watch's change events (Added, Modified, Deleted), its initial
// events (before a watch-list's bookmark) excluded.
func changeEvents(in Input, evs []WEvent) []int {
	var cs []int
	seen := in.SendInit != 2
	for i, ev := range evs {
		if ev.Type == WBookmark {
			seen = true
		}
		if seen && ev.Type <= WDeleted {
			cs = append(cs, i)
		}
	}
	return cs
}

// TestWatchCorrupt runs the driver with watchers on one member, corrupting the first watch the
// corruption applies to (corruptions; K8SETCD3_SCHED names one, all by default): porcupine then
// answers Illegal, and Ok for "none".
func TestWatchCorrupt(t *testing.T) {
	only := os.Getenv("K8SETCD3_SCHED")
	for name, f := range corruptions {
		if only != "" && name != only {
			continue
		}
		t.Run(name, func(t *testing.T) {
			inChild(t, "TestWatchCorrupt", name, func(t *testing.T) {
				var done atomic.Bool
				hook := func(in Input, out Output) Output {
					if in.Kind != KWatch || out.WFailed || done.Load() {
						return out
					}
					evs, _ := decodeWEvents(out.WEvents)
					cs := changeEvents(in, evs)
					if len(cs) == 0 {
						return out
					}
					evs2, ok := f(append([]WEvent{}, evs...), cs)
					if ok && done.CompareAndSwap(false, true) {
						out.WEvents = encodeWEvents(evs2)
						t.Logf("corrupted (%s) a watch of %q with %d change events", name, in.WKey, len(cs))
					}
					return out
				}
				// small traffic: porcupine searches exhaustively before it answers Illegal; a run
				// in which no watch had an event to corrupt is retried on a fresh member
				var r porcupine.CheckResult
				for a := 0; a < 4 && !done.Load(); a++ {
					r = singleWAt(t, a, 4, 60, 8, 6, hook)
				}
				if !done.Load() {
					t.Fatalf("no watch had a change event to corrupt in 4 runs")
				}
				want := porcupine.Illegal
				if name == "none" {
					want = porcupine.Ok
				}
				if r != want {
					t.Fatalf("got %v, want %v", r, want)
				}
			})
		})
	}
}

// clusterWatch is MainPartition's setup at k members (startCluster, newStore; the schedule sched
// run by cluster3.Partitioner if not nil) and checkWWith with the counts in ws.
func clusterWatch(t *testing.T, k uint64, clients, ops, watchers, wops int, sched []cluster3.Step,
	ws *watchStats) porcupine.CheckResult {
	srvs, brs, kc, ok := startCluster(k, zap.NewNop())
	if !ok {
		t.Fatal("startCluster")
	}
	decodeMode(t)
	s, st0, h0, ok := newStore(kc)
	if !ok {
		t.Fatal("store")
	}
	if sched != nil {
		go cluster3.Partitioner(srvs, brs, sched)
	}
	return checkWWith(s, st0, h0, clients, ops, watchers, wops, ws.hook)
}

// TestMainClusterWatch runs MainCluster's setup with watchers at testK members, in a process of its
// own: Ok, and the counts.
func TestMainClusterWatch(t *testing.T) {
	k := testK(t)
	inChild(t, "TestMainClusterWatch", "", func(t *testing.T) {
		ws := &watchStats{}
		start := time.Now()
		r := clusterWatch(t, k, 4, 120, 8, 12, nil, ws)
		ws.log(t)
		t.Logf("k=%d: %v in %v, peak RSS %s", k, r, time.Since(start), peakRSS())
		if r != porcupine.Ok {
			t.Fatalf("got %v, want Ok", r)
		}
	})
}

// TestMainPartitionWatch runs MainPartition's setup with watchers at testK members once per
// schedule (K8SETCD3_SCHED names one), each in a process of its own: Ok, the counts, the time and
// the peak memory.
func TestMainPartitionWatch(t *testing.T) {
	only := os.Getenv("K8SETCD3_SCHED")
	k := testK(t)
	scheds := partitionSchedules(int(k))
	// no leader anywhere for 6s (every peer link cut), longer than the 3 election timeouts after
	// which a member cancels its require-leader streams (the store's watches): the watches end with
	// a no-leader error (at k = 1 there is no link to cut)
	var noleader []cluster3.Step
	for a := 0; a < int(k); a++ {
		for b := a + 1; b < int(k); b++ {
			noleader = append(noleader, cluster3.Step{Kind: cluster3.PeerCut, A: a, B: b})
		}
	}
	if len(noleader) > 0 {
		noleader[0].Delay = 300 * time.Millisecond
		n := len(noleader)
		for i := 0; i < n; i++ {
			s := noleader[i]
			s.Kind = cluster3.PeerMend
			s.Delay = 0
			if i == 0 {
				s.Delay = 6 * time.Second
			}
			noleader = append(noleader, s)
		}
		scheds["noleader"] = noleader
	}
	for name, sched := range scheds {
		if only != "" && name != only {
			continue
		}
		t.Run(name, func(t *testing.T) {
			inChild(t, "TestMainPartitionWatch", name, func(t *testing.T) {
				ws := &watchStats{}
				start := time.Now()
				r := clusterWatch(t, k, 4, 120, 8, 12, sched, ws)
				ws.log(t)
				t.Logf("k=%d %s: %v in %v, peak RSS %s", k, name, r, time.Since(start), peakRSS())
				if r != porcupine.Ok {
					t.Fatalf("got %v, want Ok", r)
				}
			})
		})
	}
}
