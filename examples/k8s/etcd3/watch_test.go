package etcd3

import (
	"math/rand"
	"strconv"
	"testing"
)

// Stage B's tests of the watch check (notes/k8s-7f6-scope.md §5): the check on hand-made histories,
// and the generator's cases with the requests the proof assumes (KWatchStream.lean's WatchInOk).
// The real runs with watchers come with the driver's wiring (stage E; branch k8s-7f6-target).

// scopeOf is a watch's scope: 0 the cluster, 1 a namespace, 2 an object.
func scopeOf(in Input) int {
	if in.WKey == ResourcePrefix+"/" {
		return 0
	}
	rest := in.WKey[len(ResourcePrefix)+1:]
	for i := 0; i < len(rest); i++ {
		if rest[i] == '/' {
			return 2
		}
	}
	return 1
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
		in := genWatchFrom(rng.Uint64(), 7, cached, hasC)
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
