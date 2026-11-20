package etcd3

// Stage 7g evidence (notes/k8s-7g-scope.md §1.2, §8): the facts the Scope's trust-boundary specs and
// departures rest on, on the driver's own types.

import (
	"errors"
	"reflect"
	"strings"
	"testing"

	metav1 "k8s.io/apimachinery/pkg/apis/meta/v1"
	"k8s.io/apimachinery/pkg/runtime"
	"k8s.io/apimachinery/pkg/watch"
	"k8s.io/apiserver/pkg/storage"

	"github.com/mit-pdos/etcd-grove/examples/k8s/etcd3/correctness"
)

// reflect.DeepEqual on the values the checker compares: objects by their fields, lists by items
// (nil and empty Items differ), the remaining count by its pointee, storage errors by code, key,
// resource version and inner error (two errors.New of one message are deeply equal), sentinels by
// identity or message, different dynamic types never.
func TestDeepEqualFacts(t *testing.T) {
	o := func(v string, rv uint64) *Obj {
		return &Obj{Namespace: "ns-1", Name: "pod-1", Value: v, ResourceVersion: rv}
	}
	n1, n2 := int64(1), int64(1)
	cases := []struct {
		name string
		a, b any
		eq   bool
	}{
		{"obj same fields", runtime.Object(o("x", 3)), runtime.Object(o("x", 3)), true},
		{"obj value", runtime.Object(o("x", 3)), runtime.Object(o("y", 3)), false},
		{"obj rv", runtime.Object(o("x", 3)), runtime.Object(o("x", 4)), false},
		{"obj annotated", runtime.Object(o("x", 3)), runtime.Object(&Obj{Namespace: "ns-1", Name: "pod-1", Value: "x", ResourceVersion: 3, Annotated: true}), false},
		{"obj vs list", runtime.Object(o("x", 3)), runtime.Object(&ObjList{}), false},
		{"nil vs obj", nil, runtime.Object(o("x", 3)), false},
		{"list nil vs empty items", runtime.Object(&ObjList{ResourceVersion: 5}), runtime.Object(&ObjList{Items: []Obj{}, ResourceVersion: 5}), false},
		{"list empty items", runtime.Object(&ObjList{Items: []Obj{}, ResourceVersion: 5}), runtime.Object(&ObjList{Items: []Obj{}, ResourceVersion: 5}), true},
		{"list remaining pointee", runtime.Object(&ObjList{Items: []Obj{}, RemainingItemCount: &n1}), runtime.Object(&ObjList{Items: []Obj{}, RemainingItemCount: &n2}), true},
		{"list remaining nil", runtime.Object(&ObjList{Items: []Obj{}, RemainingItemCount: &n1}), runtime.Object(&ObjList{Items: []Obj{}}), false},
		{"not found", error(storage.NewKeyNotFoundError("/registry/objs/a", 4)), error(storage.NewKeyNotFoundError("/registry/objs/a", 4)), true},
		{"not found rv", error(storage.NewKeyNotFoundError("/registry/objs/a", 4)), error(storage.NewKeyNotFoundError("/registry/objs/a", 5)), false},
		{"invalid same msg", error(storage.NewInvalidObjError("k", "Precondition failed: x")), error(storage.NewInvalidObjError("k", "Precondition failed: x")), true},
		{"invalid other msg", error(storage.NewInvalidObjError("k", "Precondition failed: x")), error(storage.NewInvalidObjError("k", "Precondition failed: y")), false},
		{"sentinel itself", error(errUpdateRejected), error(errUpdateRejected), true},
		{"sentinels differ", error(errUpdateRejected), error(errDeleteRejected), false},
		{"errors.New same text", errors.New("a"), errors.New("a"), true},
		{"response", correctness.Response{Object: o("x", 3)}, correctness.Response{Object: o("x", 3)}, true},
		{"response err", correctness.Response{Err: storage.NewKeyExistsError("k", 0)}, correctness.Response{Err: storage.NewKeyExistsError("k", 0)}, true},
		{"map", map[string]runtime.Object{"a": o("x", 3)}, map[string]runtime.Object{"a": o("x", 3)}, true},
		{"map extra key", map[string]runtime.Object{"a": o("x", 3)}, map[string]runtime.Object{"a": o("x", 3), "b": o("x", 3)}, false},
		{"empty map vs nil map", map[string]runtime.Object{}, map[string]runtime.Object(nil), false},
	}
	for _, tc := range cases {
		if got := reflect.DeepEqual(tc.a, tc.b); got != tc.eq {
			t.Errorf("%s: DeepEqual %v, want %v", tc.name, got, tc.eq)
		}
	}
}

// The two places the maintainers' WatchValidator is stricter than the driver's check (the 7f
// Scope's departures 1 and 2): an Error event that is not the last, and a watch-list whose events
// end before the initial-events-end bookmark. Both are rejected; truncated at the Error, or with
// no initial event, they are accepted.
func TestValidatorDepartures(t *testing.T) {
	st0 := mstore{items: []item{{key: "ns-1/pod-1", obj: Obj{Namespace: "ns-1", Name: "pod-1", Value: "x", ResourceVersion: 2}, canon: true}}, rv: 2}
	init := initialModel(st0)
	// one write: an update of pod-1 to "y" at RV 3
	in := Input{Kind: KUpdate, Key: "ns-1/pod-1", Val: "y"}
	req := correctness.Request{Op: correctness.OpUpdate, Key: storeKey(in.Key), Update: correctness.UpdateRequest{UpdateFunc: tryUpdateFor(in)}}
	y := &Obj{Namespace: "ns-1", Name: "pod-1", Value: "y", ResourceVersion: 3}
	replay, err := correctness.NewReplay(init, []correctness.Operation{{Request: req, Response: correctness.Response{Object: y}}})
	if err != nil {
		t.Fatal(err)
	}
	v := correctness.NewWatchValidator(versioner{}, replay, keyFunc)
	tr := true
	pred := storage.Everything
	pred.AllowWatchBookmarks = true
	wl := correctness.WatchRequest{Key: "/objs/", Options: storage.ListOptions{Recursive: true, SendInitialEvents: &tr,
		ResourceVersionMatch: metav1.ResourceVersionMatchNotOlderThan, Predicate: pred}}
	x := &Obj{Namespace: "ns-1", Name: "pod-1", Value: "x", ResourceVersion: 2}
	errEv := watch.Event{Type: watch.Error, Object: &metav1.Status{Status: metav1.StatusFailure}}
	cases := []struct {
		name string
		evs  []watch.Event
		ok   bool
	}{
		{"full watch-list", []watch.Event{{Type: watch.Added, Object: x}, bookmark(2), {Type: watch.Modified, Object: y}}, true},
		{"error last", []watch.Event{{Type: watch.Added, Object: x}, bookmark(2), errEv}, true},
		{"error in the middle (departure 1)", []watch.Event{{Type: watch.Added, Object: x}, bookmark(2), errEv, {Type: watch.Modified, Object: y}}, false},
		{"cut before the bookmark (departure 2)", []watch.Event{{Type: watch.Added, Object: x}}, false},
		{"cut before any event", nil, true},
	}
	for _, tc := range cases {
		err := v.ValidateWatch(wl, correctness.WatchResponse{Events: tc.evs})
		if (err == nil) != tc.ok {
			t.Errorf("%s: %v, want ok %v", tc.name, err, tc.ok)
		} else if err != nil {
			t.Logf("%s: rejected: %s", tc.name, strings.SplitN(err.Error(), "\n", 2)[0])
		}
	}
	// a stale list at a revision before the initial Model's is not in the replay
	l := listInput()
	l.MinRV = rvBytes(1)
	l.Match = MExact
	err = replay.Validate(correctness.Request{Op: correctness.OpList, Key: l.ListKey, List: correctness.ListRequest{Options: listOptions(l)}},
		correctness.Response{Object: &ObjList{Items: []Obj{}, ResourceVersion: 1}})
	t.Logf("Exact list at RV 1 < the initial RV 2: %v", err)
	if err == nil {
		t.Errorf("want an error")
	}
}

func listInput() Input {
	return Input{Kind: KList, ListKey: ResourcePrefix + "/", Recursive: true}
}
