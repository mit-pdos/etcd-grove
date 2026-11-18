package etcd3

// Stage 7g step 1 evidence (notes/k8s-7g-trust.md): the Go facts each trust-boundary spec of the
// maintainers' checker states, one test per spec, on the driver's own types. Each test names the
// Lean spec it backs.

import (
	"errors"
	"maps"
	"math/rand"
	"reflect"
	"slices"
	"testing"

	apierrors "k8s.io/apimachinery/pkg/api/errors"
	"k8s.io/apimachinery/pkg/api/meta"
	"k8s.io/apimachinery/pkg/runtime"
	"k8s.io/apimachinery/pkg/runtime/schema"
	"k8s.io/apiserver/pkg/storage"

	"github.com/mit-pdos/etcd-grove/examples/k8s/etcd3/correctness"
)

// ---------------------------------------------------------------------------------------------
// reflect.DeepEqual (Spec/reflect/DeepEqualK8s.lean, reflect.DeepEqual.spec_k8s)

// A dview mirrors the Lean `k8sDeep.DeepV`: the deep value of an interface value the checker
// passes to DeepEqual. kind: 0 nil, 1 *Obj, 2 *ObjList, 3 *storage.StorageError, 4 *errorString.
type dview struct {
	kind     int
	obj      Obj   // 1
	itemsNil bool  // 2: Items is nil
	items    []Obj // 2: else these
	rv       uint64
	cont     string
	remSet   bool // 2: RemainingItemCount non-nil
	rem      int64
	code     int // 3
	key      string
	srv      int64
	inner    *dview // 3: nil, 3 or 4 (an error)
	s        string // 4
}

// viewEq is Lean's `=` on DeepV.
func viewEq(a, b *dview) bool {
	if a.kind != b.kind {
		return false
	}
	switch a.kind {
	case 0:
		return true
	case 1:
		return a.obj == b.obj
	case 2:
		if a.itemsNil != b.itemsNil || a.rv != b.rv || a.cont != b.cont || a.remSet != b.remSet {
			return false
		}
		if a.remSet && a.rem != b.rem {
			return false
		}
		return a.itemsNil || slices.Equal(a.items, b.items)
	case 3:
		return a.code == b.code && a.key == b.key && a.srv == b.srv && viewEq(a.inner, b.inner)
	case 4:
		return a.s == b.s
	}
	panic("kind")
}

var smallStrs = []string{"", "a", "b"}

func rstr(r *rand.Rand) string { return smallStrs[r.Intn(len(smallStrs))] }

func robj(r *rand.Rand) Obj {
	return Obj{Namespace: rstr(r), Name: rstr(r), UID: rstr(r), Value: rstr(r), Node: rstr(r),
		App: rstr(r), ResourceVersion: uint64(r.Intn(3)), Annotated: r.Intn(4) == 0}
}

// rview draws a view of the given kinds.
func rview(r *rand.Rand, kinds []int, depth int) *dview {
	v := &dview{kind: kinds[r.Intn(len(kinds))]}
	switch v.kind {
	case 1:
		v.obj = robj(r)
	case 2:
		v.itemsNil = r.Intn(3) == 0
		if !v.itemsNil {
			for i := r.Intn(3); i > 0; i-- {
				v.items = append(v.items, robj(r))
			}
		}
		v.rv = uint64(r.Intn(3))
		v.cont = rstr(r)
		v.remSet = r.Intn(2) == 0
		v.rem = int64(r.Intn(2))
	case 3:
		v.code = 1 + r.Intn(7)
		v.key = rstr(r)
		v.srv = int64(r.Intn(3))
		ik := []int{0, 4}
		if depth < 2 {
			ik = append(ik, 3)
		}
		v.inner = rview(r, ik, depth+1)
	case 4:
		v.s = rstr(r)
	}
	return v
}

// mutate returns a copy of v, possibly changed in one place (so that equal and nearly equal
// pairs are frequent).
func mutate(r *rand.Rand, v *dview) *dview {
	c := *v
	c.items = slices.Clone(v.items)
	if v.inner != nil {
		c.inner = mutate(r, v.inner)
	}
	if r.Intn(2) == 0 {
		return &c
	}
	switch c.kind {
	case 1:
		c.obj.Value = rstr(r)
	case 2:
		switch r.Intn(5) {
		case 0:
			c.itemsNil = !c.itemsNil
			if c.itemsNil {
				c.items = nil
			}
		case 1:
			if len(c.items) > 0 {
				c.items[0].ResourceVersion++
			}
		case 2:
			c.remSet = !c.remSet
		case 3:
			c.rem++
		case 4:
			c.cont = rstr(r)
		}
	case 3:
		c.srv = int64(r.Intn(3))
	case 4:
		c.s = rstr(r)
	}
	return &c
}

// materialize builds a fresh Go value of the view: a nil interface, or a fresh pointer (an Items
// slice with random spare capacity; a non-nil empty Items as either []Obj{} or a sub-slice of a
// larger array).
func materialize(r *rand.Rand, v *dview) any {
	switch v.kind {
	case 0:
		return nil
	case 1:
		o := v.obj
		return &o
	case 2:
		l := &ObjList{ResourceVersion: v.rv, Continue: v.cont}
		if !v.itemsNil {
			buf := make([]Obj, len(v.items), len(v.items)+r.Intn(3))
			copy(buf, v.items)
			l.Items = buf
		}
		if v.remSet {
			n := v.rem
			l.RemainingItemCount = &n
		}
		return l
	case 3:
		var inner error
		if x := materialize(r, v.inner); x != nil {
			inner = x.(error)
		}
		e := storage.NewCorruptObjError(v.key, inner)
		e.Code = v.code
		e.ResourceVersion = v.srv
		return e
	case 4:
		return errors.New(v.s)
	}
	panic("kind")
}

func asObject(x any) runtime.Object {
	if x == nil {
		return nil
	}
	return x.(runtime.Object)
}

func asError(x any) error {
	if x == nil {
		return nil
	}
	return x.(error)
}

// The spec's three clauses, on random views: (1) two interface values (runtime.Object or error,
// passed as `any`), (2) two correctness.Response, (3) two map[string]runtime.Object; DeepEqual is
// equality of the views. Each pair is also compared with the second value the same pointer as the
// first when the views are equal (DeepEqual's identity shortcut).
func TestDeepEqualViews(t *testing.T) {
	r := rand.New(rand.NewSource(7))
	objKinds := []int{0, 1, 2}
	errKinds := []int{0, 3, 4}
	all := []int{0, 1, 2, 3, 4}
	n := 0
	for i := 0; i < 20000; i++ {
		a := rview(r, all, 0)
		b := mutate(r, a)
		if r.Intn(4) == 0 {
			b = rview(r, all, 0)
		}
		xa, xb := materialize(r, a), materialize(r, b)
		if got, want := reflect.DeepEqual(xa, xb), viewEq(a, b); got != want {
			t.Fatalf("values %+v %+v: DeepEqual %v, views equal %v", a, b, got, want)
		}
		if viewEq(a, b) && !reflect.DeepEqual(xa, xa) {
			t.Fatalf("value %+v not DeepEqual to itself", a)
		}
		n++
	}
	for i := 0; i < 20000; i++ {
		oa, ea := rview(r, objKinds, 0), rview(r, errKinds, 0)
		ob, eb := mutate(r, oa), mutate(r, ea)
		if r.Intn(4) == 0 {
			ob = rview(r, objKinds, 0)
		}
		ra := correctness.Response{Object: asObject(materialize(r, oa)), Err: asError(materialize(r, ea))}
		rb := correctness.Response{Object: asObject(materialize(r, ob)), Err: asError(materialize(r, eb))}
		if got, want := reflect.DeepEqual(ra, rb), viewEq(oa, ob) && viewEq(ea, eb); got != want {
			t.Fatalf("responses (%+v,%+v) (%+v,%+v): DeepEqual %v, views equal %v", oa, ea, ob, eb, got, want)
		}
		n++
	}
	keys := []string{"/registry/objs/a", "/registry/objs/b", "c"}
	for i := 0; i < 20000; i++ {
		va, vb := map[string]*dview{}, map[string]*dview{}
		for _, k := range keys {
			if r.Intn(3) > 0 {
				va[k] = rview(r, objKinds, 0)
				if r.Intn(4) > 0 {
					vb[k] = mutate(r, va[k])
				}
			} else if r.Intn(4) == 0 {
				vb[k] = rview(r, objKinds, 0)
			}
		}
		ma, mb := map[string]runtime.Object{}, map[string]runtime.Object{}
		for k, v := range va {
			ma[k] = asObject(materialize(r, v))
		}
		for k, v := range vb {
			mb[k] = asObject(materialize(r, v))
		}
		want := len(va) == len(vb)
		for k, v := range va {
			w, ok := vb[k]
			want = want && ok && viewEq(v, w)
		}
		if got := reflect.DeepEqual(ma, mb); got != want {
			t.Fatalf("maps %v %v: DeepEqual %v, views equal %v", va, vb, got, want)
		}
		if !reflect.DeepEqual(ma, ma) {
			t.Fatalf("map not DeepEqual to itself")
		}
		n++
	}
	t.Logf("%d pairs", n)
}

// The cases the spec relies on, named (beside TestDeepEqualFacts): unexported fields are
// compared (a StorageError's inner error, an errorString's text); a typed nil pointer in an
// interface is not a nil interface (the spec's `nil` view is the nil interface only); the
// Items capacity is not compared; a nil map value differs from an object.
func TestDeepEqualNamedCases(t *testing.T) {
	o := &Obj{Name: "a", ResourceVersion: 3}
	cases := []struct {
		name string
		a, b any
		eq   bool
	}{
		{"inner error compared", storage.NewInvalidObjError("k", "x"), storage.NewInvalidObjError("k", "y"), false},
		{"inner nil vs errorString", storage.NewKeyNotFoundError("k", 1), storage.NewCorruptObjError("k", nil), false},
		{"errorString by text", errors.New("x"), errors.New("x"), true},
		{"errorString vs StorageError", errors.New("x"), storage.NewInvalidObjError("k", "x"), false},
		{"typed nil *Obj vs nil", correctness.Response{Object: (*Obj)(nil)}, correctness.Response{}, false},
		{"capacity ignored", &ObjList{Items: make([]Obj, 1, 1)}, &ObjList{Items: make([]Obj, 1, 5)}, true},
		{"same pointer", runtime.Object(o), runtime.Object(o), true},
		{"map nil value vs obj", map[string]runtime.Object{"a": nil}, map[string]runtime.Object{"a": o}, false},
		{"map nil value vs missing", map[string]runtime.Object{"a": nil}, map[string]runtime.Object{"b": nil}, false},
		{"response obj vs list", correctness.Response{Object: o}, correctness.Response{Object: &ObjList{}}, false},
	}
	for _, tc := range cases {
		if got := reflect.DeepEqual(tc.a, tc.b); got != tc.eq {
			t.Errorf("%s: DeepEqual %v, want %v", tc.name, got, tc.eq)
		}
	}
}

// ---------------------------------------------------------------------------------------------
// maps.Keys + slices.Sorted (Spec/maps/Keys.lean, maps.Keys.spec_objMap)

// slices.Sorted(maps.Keys(m)) on a map[string]runtime.Object: the keys, each once, strictly
// increasing in Go's string order (bytewise, invalid UTF-8 included); nil for an empty map
// (which `s ↦* []` holds of); maps.Keys reads the map only when iterated (a key added after the
// call to maps.Keys and before the iteration is listed); iterating twice reads the map twice.
func TestMapsKeysSorted(t *testing.T) {
	r := rand.New(rand.NewSource(3))
	alpha := []string{"", "a", "b", "B", "\xff", "\x00", "é", "ab", "a\xff"}
	for i := 0; i < 5000; i++ {
		m := map[string]runtime.Object{}
		for j := r.Intn(8); j > 0; j-- {
			m[alpha[r.Intn(len(alpha))]+alpha[r.Intn(len(alpha))]] = &Obj{}
		}
		ks := slices.Sorted(maps.Keys(m))
		if len(ks) != len(m) {
			t.Fatalf("%d keys for %d entries", len(ks), len(m))
		}
		for j, k := range ks {
			if _, ok := m[k]; !ok {
				t.Fatalf("key %q not in the map", k)
			}
			if j > 0 && !(ks[j-1] < k) {
				t.Fatalf("not strictly increasing: %q, %q", ks[j-1], k)
			}
		}
	}
	if ks := slices.Sorted(maps.Keys(map[string]runtime.Object{})); ks != nil {
		t.Errorf("empty map: %v, want nil", ks)
	}
	m := map[string]runtime.Object{"b": nil}
	seq := maps.Keys(m)
	m["a"] = nil
	if ks := slices.Sorted(seq); !slices.Equal(ks, []string{"a", "b"}) {
		t.Errorf("lazy: %v", ks)
	}
	delete(m, "b")
	if ks := slices.Sorted(seq); !slices.Equal(ks, []string{"a"}) {
		t.Errorf("second iteration: %v", ks)
	}
	if !("Z" < "a" && "a" < "\xff" && "" < "\x00") {
		t.Errorf("string order")
	}
}

// maps.Keys(m) never panics and returns a non-nil func (the post's `f : GoFunc`): on a nil map,
// an empty map and a non-empty one, the call returns normally and its result is not nil.
func TestMapsKeysNoPanic(t *testing.T) {
	var nilMap map[string]runtime.Object
	for _, m := range []map[string]runtime.Object{nilMap, {}, {"a": &Obj{}, "b": nil}} {
		func() {
			defer func() {
				if r := recover(); r != nil {
					t.Fatalf("maps.Keys panicked: %v", r)
				}
			}()
			if seq := maps.Keys(m); seq == nil {
				t.Errorf("maps.Keys(%v) returned a nil func", m)
			}
		}()
	}
}

// ---------------------------------------------------------------------------------------------
// maps.Clone, maps.Equal (Spec/maps/Clone.lean, Spec/maps/Equal.lean)

// maps.Clone of a non-nil map[string]bool: a fresh non-nil map with the same entries (a write to
// either is not seen by the other); of a nil map, nil (outside the spec: its points-to excludes
// nil maps). maps.Equal of two map[string]bool: the same entries (a false entry differs from no
// entry); nil and empty are Equal (outside the spec).
func TestMapsCloneEqual(t *testing.T) {
	r := rand.New(rand.NewSource(5))
	for i := 0; i < 5000; i++ {
		a, b := map[string]bool{}, map[string]bool{}
		for _, k := range smallStrs {
			if r.Intn(2) == 0 {
				a[k] = r.Intn(2) == 0
			}
			if r.Intn(2) == 0 {
				b[k] = r.Intn(2) == 0
			}
		}
		same := len(a) == len(b)
		for k, v := range a {
			w, ok := b[k]
			same = same && ok && v == w
		}
		if maps.Equal(a, b) != same {
			t.Fatalf("Equal(%v, %v) = %v", a, b, !same)
		}
		c := maps.Clone(a)
		if c == nil || !maps.Equal(a, c) || len(c) != len(a) {
			t.Fatalf("Clone(%v) = %v", a, c)
		}
		c["new"] = true
		if _, ok := a["new"]; ok {
			t.Fatalf("Clone shares the map")
		}
	}
	if maps.Clone(map[string]bool{}) == nil {
		t.Errorf("Clone of an empty non-nil map is nil")
	}
	if maps.Clone(map[string]bool(nil)) != nil {
		t.Errorf("Clone of nil is not nil")
	}
	if maps.Equal(map[string]bool{"a": false}, map[string]bool{}) {
		t.Errorf("a false entry Equal to no entry")
	}
	if !maps.Equal(map[string]bool{}, map[string]bool(nil)) {
		t.Errorf("empty and nil not Equal")
	}
}

// ---------------------------------------------------------------------------------------------
// meta.SetList (Spec/k8s_io/apimachinery/pkg/api/meta/SetList.lean, meta.SetList.spec_objList)

// meta.SetList(list, objects) with list a non-nil *ObjList and objects a []runtime.Object of
// non-nil *Obj: returns nil, and sets list.Items to a fresh non-nil slice of copies of the
// objects (empty and non-nil when objects is nil or empty); the other fields unchanged; later
// writes to the objects are not seen.
func TestSetListObjList(t *testing.T) {
	for n := 0; n < 4; n++ {
		for _, nilObjs := range []bool{false, true} {
			if nilObjs && n > 0 {
				continue
			}
			var objs []runtime.Object
			if !nilObjs {
				objs = []runtime.Object{}
			}
			var want []Obj
			for i := 0; i < n; i++ {
				o := &Obj{Name: string(rune('a' + i)), ResourceVersion: uint64(i)}
				objs = append(objs, o)
				want = append(want, *o)
			}
			cnt := int64(9)
			l := &ObjList{Items: []Obj{{Name: "old"}}, ResourceVersion: 4, Continue: "c", RemainingItemCount: &cnt}
			if err := meta.SetList(l, objs); err != nil {
				t.Fatalf("n=%d: %v", n, err)
			}
			if l.Items == nil {
				t.Fatalf("n=%d nil=%v: Items nil", n, nilObjs)
			}
			if !slices.Equal(l.Items, want) {
				t.Fatalf("n=%d: Items %v, want %v", n, l.Items, want)
			}
			if l.ResourceVersion != 4 || l.Continue != "c" || l.RemainingItemCount != &cnt {
				t.Fatalf("other fields changed: %+v", l)
			}
			if n > 0 {
				objs[0].(*Obj).Value = "changed"
				if l.Items[0].Value != "" {
					t.Fatalf("Items share the objects")
				}
			}
		}
	}
}

// ---------------------------------------------------------------------------------------------
// apierrors: SuggestsClientDelay, IsTooManyRequests and the status checks on the errors the
// checker sees (Spec/k8s_io/apimachinery/pkg/api/errors/{SuggestsClientDelay,IsTooManyRequests}.lean,
// the extended `.plain` view of View.lean)

// The errors the checker passes to apierrors' checks: nil, *storage.StorageError (inner nil or
// an errors.New), an errors.New, and storage's too-large *StatusError. *StorageError is no
// APIStatus (it has no Status method) and unwraps to its inner error.
func checkerErrs() map[string]error {
	return map[string]error{
		"nil":          nil,
		"notFound":     storage.NewKeyNotFoundError("/registry/objs/a", 4),
		"exists":       storage.NewKeyExistsError("/registry/objs/a", 0),
		"invalidObj":   storage.NewInvalidObjError("/registry/objs/a", "Precondition failed: x"),
		"errorString":  errors.New("k8setcd3: update rejected"),
		"setOnCreate":  storage.ErrResourceVersionSetOnCreate,
		"tooLarge0":    storage.NewTooLargeResourceVersionError(5, 4, 0),
		"tooLarge2":    storage.NewTooLargeResourceVersionError(5, 4, 2),
		"serverTO":     apierrors.NewServerTimeout(schema.GroupResource{Resource: "pods"}, "get", 3),
		"tooMany":      apierrors.NewTooManyRequests("x", 4),
		"tooManyNoRA":  apierrors.NewTooManyRequests("x", 0),
		"resourceGone": apierrors.NewResourceExpired("x"),
	}
}

func TestStorageErrorNotAPIStatus(t *testing.T) {
	var e error = storage.NewKeyNotFoundError("k", 1)
	if _, ok := e.(apierrors.APIStatus); ok {
		t.Errorf("*StorageError is an APIStatus")
	}
	var s apierrors.APIStatus
	if errors.As(e, &s) || errors.As(storage.NewInvalidObjError("k", "m"), &s) {
		t.Errorf("errors.As finds an APIStatus in a StorageError")
	}
}

// SuggestsClientDelay: (0, false) on nil, a StorageError, an errors.New; on a *StatusError with
// details, (RetryAfterSeconds, true) if the reason is ServerTimeout or RetryAfterSeconds > 0, else
// (0, false); on one with nil details, (0, false). storage's too-large error with retry 0 is
// (0, false): the Model's validateGet/validateList reject such an output on a stale read.
func TestSuggestsClientDelay(t *testing.T) {
	want := map[string]struct {
		n  int
		ok bool
	}{
		"nil": {0, false}, "notFound": {0, false}, "exists": {0, false}, "invalidObj": {0, false},
		"errorString": {0, false}, "setOnCreate": {0, false}, "tooLarge0": {0, false},
		"tooLarge2": {2, true}, "serverTO": {3, true}, "tooMany": {4, true}, "tooManyNoRA": {0, false},
		"resourceGone": {0, false},
	}
	for name, err := range checkerErrs() {
		n, ok := apierrors.SuggestsClientDelay(err)
		if w := want[name]; n != w.n || ok != w.ok {
			t.Errorf("%s: (%d, %v), want (%d, %v)", name, n, ok, w.n, w.ok)
		}
		if se, isSE := err.(*apierrors.StatusError); isSE {
			st := se.Status()
			wn, wok := 0, false
			if st.Details != nil {
				if st.Reason == "ServerTimeout" || st.Details.RetryAfterSeconds > 0 {
					wn, wok = int(st.Details.RetryAfterSeconds), true
				}
			}
			if n != wn || ok != wok {
				t.Errorf("%s: (%d, %v), the view says (%d, %v)", name, n, ok, wn, wok)
			}
		}
	}
	se := &apierrors.StatusError{}
	se.ErrStatus.Reason = "ServerTimeout"
	if n, ok := apierrors.SuggestsClientDelay(se); n != 0 || ok {
		t.Errorf("nil details: (%d, %v)", n, ok)
	}
	if !panics(func() { apierrors.SuggestsClientDelay((*apierrors.StatusError)(nil)) }) {
		t.Errorf("typed nil *StatusError: no panic")
	}
}

// IsTooManyRequests: false on nil, a StorageError, an errors.New; on a *StatusError, reason
// TooManyRequests or code 429. It panics on a typed nil *StatusError: the current spec
// ("some boolean", no precondition) is false there (finding, step 1 report).
func TestIsTooManyRequests(t *testing.T) {
	for name, err := range checkerErrs() {
		want := name == "tooMany" || name == "tooManyNoRA"
		if got := apierrors.IsTooManyRequests(err); got != want {
			t.Errorf("%s: %v", name, got)
		}
		if se, isSE := err.(*apierrors.StatusError); isSE {
			st := se.Status()
			if v := st.Reason == "TooManyRequests" || st.Code == 429; v != want {
				t.Errorf("%s: the view says %v", name, v)
			}
		}
	}
	if !panics(func() { apierrors.IsTooManyRequests((*apierrors.StatusError)(nil)) }) {
		t.Errorf("typed nil *StatusError: no panic")
	}
}

// IsTimeout, HasStatusCause and storage.IsTooLargeResourceVersion are false on nil, on a
// StorageError (inner nil or an errors.New) and on an errors.New: the extended `.plain` view.
func TestStatusChecksPlain(t *testing.T) {
	for _, name := range []string{"nil", "notFound", "exists", "invalidObj", "errorString", "setOnCreate"} {
		err := checkerErrs()[name]
		if apierrors.IsTimeout(err) || apierrors.HasStatusCause(err, "ResourceVersionTooLarge") ||
			storage.IsTooLargeResourceVersion(err) || apierrors.IsTooManyRequests(err) {
			t.Errorf("%s: a status check answers true", name)
		}
	}
	if !storage.IsTooLargeResourceVersion(checkerErrs()["tooLarge0"]) {
		t.Errorf("tooLarge0 not too large")
	}
}

// The extended `.plain` view (proposal V, M2 of the step 1 review): a wrapper is `.plain` only
// through its `Unwrap`'s `□ WP` premise, and that premise is where a typed-nil receiver is excluded:
// a typed nil *StorageError, bare or as the nil embedded pointer of a struct, panics in every
// status check (errors.As calls its Unwrap, which dereferences nil). A non-nil wrapper whose
// Unwrap returns nil or a leaf is false everywhere (the view's answer).
type embedSE struct{ *storage.StorageError }

func TestPlainWrapperTypedNil(t *testing.T) {
	var nilSE *storage.StorageError
	for name, err := range map[string]error{"typedNil": nilSE, "embeddedNil": embedSE{}} {
		for check, f := range map[string]func(error){
			"IsTimeout":           func(e error) { apierrors.IsTimeout(e) },
			"HasStatusCause":      func(e error) { apierrors.HasStatusCause(e, "x") },
			"IsTooManyRequests":   func(e error) { apierrors.IsTooManyRequests(e) },
			"SuggestsClientDelay": func(e error) { apierrors.SuggestsClientDelay(e) },
		} {
			if !panics(func() { f(err) }) {
				t.Errorf("%s(%s): no panic", check, name)
			}
		}
	}
	for _, err := range []error{embedSE{storage.NewKeyNotFoundError("k", 1)}, storage.NewInvalidObjError("k", "m")} {
		n, ok := apierrors.SuggestsClientDelay(err)
		if apierrors.IsTimeout(err) || apierrors.HasStatusCause(err, "x") || apierrors.IsTooManyRequests(err) || n != 0 || ok {
			t.Errorf("%T: a status check answers true", err)
		}
	}
}

func panics(f func()) (p bool) {
	defer func() { p = recover() != nil }()
	f()
	return false
}

// ---------------------------------------------------------------------------------------------
// meta.ListAccessor of the driver's *ObjList (Spec/k8s_io/apimachinery/pkg/api/meta/ListAccessor.lean,
// the spec's second row): the same interface value (the same pointer, a nil *ObjList included) and
// a nil error; GetContinue/SetContinue on the result act on the list.
func TestListAccessorObjList(t *testing.T) {
	n := int64(2)
	for _, l := range []*ObjList{{}, {Items: []Obj{{}}, ResourceVersion: 7, Continue: "c", RemainingItemCount: &n}, nil} {
		acc, err := meta.ListAccessor(l)
		if err != nil {
			t.Fatalf("ListAccessor(%v): error %v", l, err)
		}
		got, ok := acc.(*ObjList)
		if !ok || got != l {
			t.Fatalf("ListAccessor(%p) = %#v, want the same *ObjList", l, acc)
		}
		if l == nil {
			continue
		}
		if acc.GetContinue() != l.Continue {
			t.Errorf("GetContinue %q, want %q", acc.GetContinue(), l.Continue)
		}
		acc.SetContinue("next")
		if l.Continue != "next" {
			t.Errorf("SetContinue did not set the list's token")
		}
	}
}
