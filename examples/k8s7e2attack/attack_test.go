// Package k8s7e2attack probes, on the real k8s.io/apimachinery and k8s.io/apiserver at the pins of
// examples/k8s/etcd3/go.mod, the trusted statements of k8s etcd3 stage 7e-2's Draft
// (notes/k8s-7e-2-draft.md §5) and the claims of §6-7 they rest on. Each test names the
// statement it probes; notes/k8s-7e-2-attack.md has the verdicts.
//
// Run: GOWORK=off GOTOOLCHAIN=go1.27.3 go test ./... (under a 32G memory cap).
package k8s7e2attack

import (
	"encoding/base64"
	"encoding/json"
	"errors"
	"fmt"
	"math"
	"reflect"
	"strings"
	"testing"
	"time"
	"unsafe"

	driver "github.com/mit-pdos/etcd-grove/examples/k8s/etcd3"
	apierrors "k8s.io/apimachinery/pkg/api/errors"
	"k8s.io/apimachinery/pkg/api/meta"
	metav1 "k8s.io/apimachinery/pkg/apis/meta/v1"
	"k8s.io/apimachinery/pkg/conversion"
	"k8s.io/apimachinery/pkg/runtime/schema"
	"k8s.io/apiserver/pkg/storage"
	etcd3metrics "k8s.io/apiserver/pkg/storage/etcd3/metrics"
	storagemetrics "k8s.io/apiserver/pkg/storage/metrics"
)

// panics runs f and returns the recovered panic value (nil if none).
func panics(f func()) (r any) {
	defer func() { r = recover() }()
	f()
	return nil
}

// ---------------------------------------------------------------------------------------------
// §5.1 apierrors.IsTimeout / HasStatusCause
// ---------------------------------------------------------------------------------------------

// knownReasons is the Draft's `knownReasons` as it must be: errors.go:47-68, Unknown ("") NOT in it.
var knownReasons = []metav1.StatusReason{
	metav1.StatusReasonUnauthorized, metav1.StatusReasonForbidden, metav1.StatusReasonNotFound,
	metav1.StatusReasonAlreadyExists, metav1.StatusReasonConflict, metav1.StatusReasonGone,
	metav1.StatusReasonInvalid, metav1.StatusReasonServerTimeout, metav1.StatusReasonStoreReadError,
	metav1.StatusReasonTimeout, metav1.StatusReasonTooManyRequests, metav1.StatusReasonBadRequest,
	metav1.StatusReasonMethodNotAllowed, metav1.StatusReasonNotAcceptable,
	metav1.StatusReasonRequestEntityTooLarge, metav1.StatusReasonUnsupportedMediaType,
	metav1.StatusReasonInternalError, metav1.StatusReasonExpired, metav1.StatusReasonServiceUnavailable,
}

func known(r metav1.StatusReason) bool {
	for _, k := range knownReasons {
		if k == r {
			return true
		}
	}
	return false
}

// timeoutV is the Draft's `timeoutV st`.
func timeoutV(st metav1.Status) bool {
	return st.Reason == metav1.StatusReasonTimeout || (!known(st.Reason) && st.Code == 504)
}

func causeIn(st metav1.Status, name metav1.CauseType) bool {
	if st.Details == nil {
		return false
	}
	for _, c := range st.Details.Causes {
		if c.Type == name {
			return true
		}
	}
	return false
}

// The `.status` view: `err` is a non-nil *StatusError; IsTimeout = timeoutV, HasStatusCause = causeIn.
func TestStatusView(t *testing.T) {
	reasons := append([]metav1.StatusReason{"", "SomethingElse", "timeout"}, knownReasons...)
	codes := []int32{0, 200, 403, 410, 500, 504, -504, math.MaxInt32, math.MinInt32}
	details := []*metav1.StatusDetails{nil, {}, {Causes: []metav1.StatusCause{}},
		{Causes: []metav1.StatusCause{{Type: "A"}, {Type: metav1.CauseTypeResourceVersionTooLarge}}},
		{Causes: []metav1.StatusCause{{Type: ""}}}}
	names := []metav1.CauseType{"", "A", "B", metav1.CauseTypeResourceVersionTooLarge}
	n := 0
	for _, r := range reasons {
		for _, c := range codes {
			for _, d := range details {
				st := metav1.Status{Reason: r, Code: c, Details: d}
				var err error = &apierrors.StatusError{ErrStatus: st}
				if got, want := apierrors.IsTimeout(err), timeoutV(st); got != want {
					t.Errorf("IsTimeout(%q,%d) = %v, timeoutV = %v", r, c, got, want)
				}
				for _, nm := range names {
					if got, want := apierrors.HasStatusCause(err, nm), causeIn(st, nm); got != want {
						t.Errorf("HasStatusCause(%v,%q) = %v, want %v", d, nm, got, want)
					}
				}
				n++
			}
		}
	}
	// the edge the Lean `knownReasons` must get right: Unknown ("") is not a known reason
	if !apierrors.IsTimeout(&apierrors.StatusError{ErrStatus: metav1.Status{Code: 504}}) {
		t.Errorf("IsTimeout(reason \"\", code 504) should be true")
	}
	t.Logf("%d statuses checked", n)
}

// What the Draft's §4.5 relies on: NewTooLargeResourceVersionError is a `.status` view with
// timeoutV and the cause; the 410 of interpretListError is not a timeout.
func TestTooLargeAndExpired(t *testing.T) {
	err := storage.NewTooLargeResourceVersionError(10, 5, 0)
	se, ok := err.(*apierrors.StatusError)
	if !ok || se == nil {
		t.Fatalf("not a *StatusError: %T", err)
	}
	if !apierrors.IsTimeout(err) || !apierrors.HasStatusCause(err, metav1.CauseTypeResourceVersionTooLarge) ||
		!storage.IsTooLargeResourceVersion(err) || se.ErrStatus.Reason != metav1.StatusReasonTimeout {
		t.Errorf("too-large error: %+v", se.ErrStatus)
	}
	exp := apierrors.NewResourceExpired("x")
	if apierrors.IsTimeout(exp) || storage.IsTooLargeResourceVersion(exp) {
		t.Errorf("410 counts as a timeout")
	}
}

type plainErr struct{ s string }

func (e plainErr) Error() string { return e.s }

// A leaf type outside APIStatus's type set: false for both.
func TestPlainView(t *testing.T) {
	for _, err := range []error{errors.New("x"), fmt.Errorf("x %v", 1), plainErr{"y"}, &plainErr{"z"},
		storage.NewInternalError(errors.New("i"))} {
		if _, isAPI := err.(apierrors.APIStatus); isAPI {
			continue // not a .plain view
		}
		if apierrors.IsTimeout(err) || apierrors.HasStatusCause(err, metav1.CauseTypeResourceVersionTooLarge) {
			t.Errorf("%T: true", err)
		}
	}
	if apierrors.IsTimeout(nil) || apierrors.HasStatusCause(nil, "") {
		t.Errorf("nil: true")
	}
}

// asErr is a leaf (no Unwrap), outside APIStatus's type set, but has an `As` method:
// errors.As(err, &status) calls it, and IsTimeout returns true. The Draft's `.plain` view must
// exclude `As(any) bool` (leafErrTy), or IsTimeout's `.plain => false` is false.
type asErr struct{}

func (asErr) Error() string { return "as" }
func (asErr) As(target any) bool {
	if p, ok := target.(*apierrors.APIStatus); ok {
		*p = &apierrors.StatusError{ErrStatus: metav1.Status{Reason: metav1.StatusReasonTimeout,
			Details: &metav1.StatusDetails{Causes: []metav1.StatusCause{{Type: metav1.CauseTypeResourceVersionTooLarge}}}}}
		return true
	}
	return false
}

// unwrapErr has no Unwrap() error but Unwrap() []error (a join): also must be excluded.
type joinErr struct{ errs []error }

func (e joinErr) Error() string   { return "join" }
func (e joinErr) Unwrap() []error { return e.errs }

func TestLeafMustExcludeAsAndUnwrapSlice(t *testing.T) {
	var err error = asErr{}
	if _, isAPI := err.(apierrors.APIStatus); isAPI {
		t.Fatal("asErr implements APIStatus")
	}
	if !apierrors.IsTimeout(err) || !apierrors.HasStatusCause(err, metav1.CauseTypeResourceVersionTooLarge) ||
		!storage.IsTooLargeResourceVersion(err) {
		t.Errorf("As method not followed")
	} else {
		t.Logf("leaf non-APIStatus type with an As method: IsTimeout = true (leafErrTy must exclude As)")
	}
	j := joinErr{[]error{storage.NewTooLargeResourceVersionError(1, 0, 0)}}
	if !apierrors.IsTimeout(j) {
		t.Errorf("Unwrap() []error not followed")
	} else {
		t.Logf("non-APIStatus type with Unwrap() []error: IsTimeout = true (leafErrTy must exclude it)")
	}
	w := fmt.Errorf("wrap: %w", storage.NewTooLargeResourceVersionError(1, 0, 0))
	if !apierrors.IsTimeout(w) {
		t.Errorf("%%w not followed")
	}
}

// A typed-nil *StatusError, bare or wrapped with %w, panics in both (Status() dereferences nil,
// errors.go:75-79). Excluded from `.status` by `l ↦□ _` (typedPointsto_not_null), from `.plain`
// by the type set (and, wrapped, by leafErrTy), hence by the specs' precondition apiErrOk.
func TestTypedNilStatusError(t *testing.T) {
	var se *apierrors.StatusError
	var err error = se
	if r := panics(func() { apierrors.IsTimeout(err) }); r == nil {
		t.Errorf("typed nil: no panic")
	} else {
		t.Logf("typed-nil *StatusError: IsTimeout panics (%v)", r)
	}
	if r := panics(func() { apierrors.HasStatusCause(err, "x") }); r == nil {
		t.Errorf("typed nil: no panic")
	}
	// Wrapped with %w, errors.As finds the typed nil and Status() panics the same way: the
	// review of 2026-11-10 refuted the precondition-free IsTimeout/HasStatusCause specs with
	// these, hence their precondition apiErrOk (View.lean).
	w := fmt.Errorf("wrapped: %w", err)
	if r := panics(func() { apierrors.IsTimeout(w) }); r == nil {
		t.Errorf("wrapped typed nil: IsTimeout: no panic")
	}
	if r := panics(func() { apierrors.HasStatusCause(w, "x") }); r == nil {
		t.Errorf("wrapped typed nil: HasStatusCause: no panic")
	}
}

// ---------------------------------------------------------------------------------------------
// §5.2 reflect, §5.3 meta.GetItemsPtr (on the driver's ObjList and Obj)
// ---------------------------------------------------------------------------------------------

// itemsValue is what GetList builds: GetItemsPtr, then EnforcePtr.
func itemsValue(t *testing.T, l *driver.ObjList) reflect.Value {
	lp, err := meta.GetItemsPtr(l)
	if err != nil {
		t.Fatal(err)
	}
	v, err := conversion.EnforcePtr(lp)
	if err != nil {
		t.Fatal(err)
	}
	return v
}

func TestGetItemsPtr(t *testing.T) {
	l := &driver.ObjList{Items: []driver.Obj{{Name: "a"}}}
	lp, err := meta.GetItemsPtr(l)
	if err != nil {
		t.Fatal(err)
	}
	p, ok := lp.(*[]driver.Obj)
	if !ok || p != &l.Items {
		t.Errorf("GetItemsPtr = %T %p, want *[]Obj %p", lp, lp, &l.Items)
	}
	// nil Items: same answer
	l2 := &driver.ObjList{}
	lp2, err := meta.GetItemsPtr(l2)
	if err != nil || lp2.(*[]driver.Obj) != &l2.Items {
		t.Errorf("nil Items: %v %v", lp2, err)
	}
	// nil *ObjList: an error, not a panic (excluded by pl ≠ null)
	var ln *driver.ObjList
	lp3, err := meta.GetItemsPtr(ln)
	if err == nil || lp3 != nil {
		t.Errorf("nil list: %v %v", lp3, err)
	}
}

func TestKindLenCapIsNil(t *testing.T) {
	for _, items := range [][]driver.Obj{nil, {}, make([]driver.Obj, 0, 5), make([]driver.Obj, 3, 7)} {
		l := &driver.ObjList{Items: items}
		v := itemsValue(t, l)
		if v.Kind() != reflect.Slice || !v.CanSet() || !v.CanAddr() {
			t.Errorf("Kind/CanSet: %v %v", v.Kind(), v.CanSet())
		}
		if v.Len() != len(items) || v.Cap() != cap(items) {
			t.Errorf("Len/Cap")
		}
		if v.IsNil() != (items == nil) {
			t.Errorf("IsNil")
		}
		// the fact finalizeList needs (the Draft's IsNil post is too weak without it)
		if v.IsNil() && v.Len() != 0 {
			t.Errorf("IsNil with Len > 0")
		}
		if v.Type().Elem() != reflect.TypeOf(driver.Obj{}) {
			t.Errorf("Type.Elem")
		}
	}
	// IsNil true drops nothing only because the slice is then empty: with Items non-empty,
	// finalizeList's Set(MakeSlice(0,0)) would lose the items. Show the effect if IsNil lied.
	l := &driver.ObjList{Items: []driver.Obj{{Name: "a"}}}
	v := itemsValue(t, l)
	v.Set(reflect.MakeSlice(v.Type(), 0, 0))
	if len(l.Items) != 0 || l.Items == nil {
		t.Errorf("Set(MakeSlice(0,0))")
	}
	t.Logf("Set(MakeSlice(0,0)) empties a non-empty list: `IsNil = some bool` cannot prove finalizeList")
}

func TestMakeSlice(t *testing.T) {
	rt := reflect.TypeOf([]driver.Obj(nil))
	for _, nm := range [][2]int{{0, 0}, {0, 1}, {3, 3}, {2, 2048}} {
		w := reflect.MakeSlice(rt, nm[0], nm[1])
		if w.Len() != nm[0] || w.Cap() != nm[1] || w.CanAddr() || w.IsNil() {
			t.Errorf("MakeSlice %v", nm)
		}
		s := w.Interface().([]driver.Obj)
		for _, o := range s[:cap(s)] {
			if o != (driver.Obj{}) {
				t.Errorf("not zeroed")
			}
		}
	}
	// excluded by the premise 0 ≤ n ≤ m
	for _, nm := range [][2]int{{-1, 0}, {1, 0}, {0, -1}} {
		if panics(func() { reflect.MakeSlice(rt, nm[0], nm[1]) }) == nil {
			t.Errorf("no panic %v", nm)
		}
	}
}

// **Refutation of §5.2 MakeSlice as stated**: 0 ≤ n ≤ m holds, yet Go panics when m·sizeof(Obj)
// exceeds maxAlloc (2^48 on linux/amd64): runtime.unsafe_NewArray, "allocation size out of range".
// No memory is allocated (the check precedes the allocation).
func TestMakeSliceHugeCapPanics(t *testing.T) {
	rt := reflect.TypeOf([]driver.Obj(nil))
	size := int(unsafe.Sizeof(driver.Obj{}))
	t.Logf("sizeof(Obj) = %d; maxAlloc/size = %d", size, (1<<48)/size)
	for _, m := range []int{1 << 62, math.MaxInt64, (1<<48)/size + 1} {
		r := panics(func() { reflect.MakeSlice(rt, 0, m) })
		if r == nil {
			t.Errorf("MakeSlice(rt, 0, %d): no panic", m)
		} else {
			t.Logf("MakeSlice(rt, 0, %d) panics: %v", m, r)
		}
	}
	// the same for Perennial's own make (KNOWN_LIMITATIONS: "No limit on allocation size")
	m := 1 << 62
	if r := panics(func() { _ = make([]driver.Obj, 0, m) }); r != nil {
		t.Logf("make([]Obj, 0, 1<<62) panics too: %v", r)
	}
}

func TestCopy(t *testing.T) {
	rt := reflect.TypeOf([]driver.Obj(nil))
	mk := func(names ...string) []driver.Obj {
		s := make([]driver.Obj, len(names))
		for i, n := range names {
			s[i] = driver.Obj{Name: n}
		}
		return s
	}
	for _, c := range []struct{ dst, src int }{{0, 0}, {0, 2}, {2, 2}, {3, 2}, {1, 3}} {
		src := mk([]string{"a", "b", "c"}[:c.src]...)
		l := &driver.ObjList{Items: src}
		v := itemsValue(t, l)
		w := reflect.MakeSlice(rt, c.dst, c.dst+4)
		ds := w.Interface().([]driver.Obj)
		for i := range ds {
			ds[i] = driver.Obj{Name: "z"}
		}
		before := append([]driver.Obj(nil), ds...)
		n := reflect.Copy(w, v)
		want := min(c.dst, c.src)
		if n != want {
			t.Errorf("Copy = %d want %d", n, want)
		}
		exp := append(append([]driver.Obj(nil), src[:min(c.src, c.dst)]...), before[min(c.src, c.dst):]...)
		if len(ds) != len(exp) || (len(ds) > 0 && !reflect.DeepEqual(ds, exp)) {
			t.Errorf("Copy content %v want %v", ds, exp)
		}
		if !reflect.DeepEqual(l.Items, src) {
			t.Errorf("src changed")
		}
	}
}

func TestAppendSet(t *testing.T) {
	for _, items := range [][]driver.Obj{nil, {}, make([]driver.Obj, 1, 1), make([]driver.Obj, 1, 4)} {
		l := &driver.ObjList{Items: items}
		old := l.Items
		v := itemsValue(t, l)
		o := &driver.Obj{Name: "new", ResourceVersion: 7}
		e := reflect.ValueOf(o).Elem()
		if !e.CanSet() {
			t.Errorf("ValueOf(ptr).Elem not settable")
		}
		w := reflect.Append(v, e)
		if w.CanAddr() || w.Len() != len(items)+1 {
			t.Errorf("Append")
		}
		// Append does not touch the variable (p ↦ s stays)
		if len(l.Items) != len(old) {
			t.Errorf("Append changed the variable")
		}
		o.Name = "mutated" // the element was copied
		v.Set(w)
		if l.Items[len(l.Items)-1].Name != "new" {
			t.Errorf("element aliased the source")
		}
		// with spare capacity the result shares the old backing array (hence the spec consumes
		// `s ↦* os ∗ ownSliceCap s`, as Perennial's append)
		if cap(items) > len(items) && &l.Items[0] != &items[:1][0] {
			t.Errorf("expected shared backing")
		}
	}
	// ValueOf of a nil *Obj: IsNil true, Elem is the invalid Value (premise p ≠ null excludes it)
	var on *driver.Obj
	vn := reflect.ValueOf(on)
	if !vn.IsNil() || vn.Elem().IsValid() {
		t.Errorf("nil ptr")
	}
}

// ---------------------------------------------------------------------------------------------
// §5.4 the continue token's encoders
// ---------------------------------------------------------------------------------------------

type continueToken struct { // continue.go:39-43, field for field (unexported in storage)
	APIVersion      string `json:"v"`
	ResourceVersion int64  `json:"rv"`
	StartKey        string `json:"start"`
}

func TestMarshalToken(t *testing.T) {
	keys := []string{"", "a", "/x/y\x00", "\xff\xfe", "<>& ", strings.Repeat("k", 1<<20), "\"\\"}
	rvs := []int64{0, 1, -1, math.MaxInt64, math.MinInt64}
	for _, k := range keys {
		for _, rv := range rvs {
			tok := &continueToken{"meta.k8s.io/v1", rv, k}
			a, err := json.Marshal(tok)
			if err != nil {
				t.Errorf("Marshal error %v", err)
			}
			b, _ := json.Marshal(tok)
			if string(a) != string(b) {
				t.Errorf("not deterministic")
			}
			if len(a) > 0 {
				a[0] = 'X' // fresh buffer: the second result unaffected
				if b[0] == 'X' {
					t.Errorf("aliased result")
				}
			}
			if *tok != (continueToken{"meta.k8s.io/v1", rv, k}) {
				t.Errorf("token changed")
			}
			// EncodeContinue = rawUrlEnc ∘ tokJson (§4.2's encL), key prefixed by "/p/"
			got, err := storage.EncodeContinue("/p/"+k+"x", "/p/", rv)
			b2, _ := json.Marshal(&continueToken{"meta.k8s.io/v1", rv, k + "x"})
			if err != nil || got != base64.RawURLEncoding.EncodeToString(b2) {
				t.Errorf("EncodeContinue mismatch")
			}
		}
	}
	// tokJson is not injective in the key (invalid UTF-8 is replaced): no property may say so
	a, _ := json.Marshal(&continueToken{"meta.k8s.io/v1", 1, "\xff"})
	b, _ := json.Marshal(&continueToken{"meta.k8s.io/v1", 1, "\xfe"})
	t.Logf("invalid UTF-8 collapses: %s == %s: %v", a, b, string(a) == string(b))
}

func TestRawURLEncoding(t *testing.T) {
	if base64.RawURLEncoding == nil {
		t.Fatal("nil")
	}
	e := base64.RawURLEncoding
	for _, d := range [][]byte{nil, {}, {0}, {0xff, 0xfe}, []byte("abcd")} {
		in := append([]byte(nil), d...)
		s1 := e.EncodeToString(d)
		s2 := e.EncodeToString(d)
		if s1 != s2 || strings.ContainsAny(s1, "=+/") || string(in) != string(d) {
			t.Errorf("RawURLEncoding %q", s1)
		}
	}
	if base64.RawURLEncoding != e {
		t.Errorf("changed")
	}
}

// ---------------------------------------------------------------------------------------------
// §5.5 the list metrics (and the existing RecordEtcdRequest, same shape)
// ---------------------------------------------------------------------------------------------

var gr = schema.GroupResource{Group: "g", Resource: "r"}
var badGr = schema.GroupResource{Group: "\xff", Resource: "r"}

// Before registration (the driver never registers): no-ops on any input.
func TestMetricsUnregistered(t *testing.T) {
	for _, g := range []schema.GroupResource{gr, badGr} {
		if r := panics(func() {
			etcd3metrics.RecordStorageListMetrics(g, "\xff", -1, -1, -1)
			etcd3metrics.RecordListLatency(g, false, time.Now().Add(time.Hour))
			etcd3metrics.RecordEtcdRequest("\xff", g, errors.New("x"), time.Now())
		}); r != nil {
			t.Errorf("unregistered: panic %v", r)
		}
	}
}

// After registration, as the apiserver does (pkg/server/routes/metrics.go:53-60):
// a negative count panics (prometheus counter Add), an invalid UTF-8 label panics
// (WithLabelValues). Runs as a subprocess-free test after TestMetricsUnregistered (go test runs
// tests in source order).
func TestMetricsRegistered(t *testing.T) {
	storagemetrics.Register()
	etcd3metrics.Register()
	cases := []struct {
		name string
		f    func()
	}{
		{"ok", func() { etcd3metrics.RecordStorageListMetrics(gr, "", 0, 0, 0) }},
		{"ok-latency", func() { etcd3metrics.RecordListLatency(gr, false, time.Now().Add(time.Hour)) }},
		{"negative fetched", func() { etcd3metrics.RecordStorageListMetrics(gr, "", -1, 0, 0) }},
		{"negative evaluated", func() { etcd3metrics.RecordStorageListMetrics(gr, "", 0, -1, 0) }},
		{"negative returned", func() { etcd3metrics.RecordStorageListMetrics(gr, "", 0, 0, -1) }},
		{"invalid UTF-8 group", func() { etcd3metrics.RecordStorageListMetrics(badGr, "", 0, 0, 0) }},
		{"invalid UTF-8 index", func() { etcd3metrics.RecordStorageListMetrics(gr, "\xff", 0, 0, 0) }},
		{"latency invalid UTF-8", func() { etcd3metrics.RecordListLatency(badGr, true, time.Now()) }},
		{"RecordEtcdRequest invalid UTF-8 verb", func() { etcd3metrics.RecordEtcdRequest("\xff", gr, nil, time.Now()) }},
		{"RecordEtcdRequest invalid UTF-8 group", func() { etcd3metrics.RecordEtcdRequest("list", badGr, errors.New("x"), time.Now()) }},
		{"RecordDecodeError invalid UTF-8 group", func() { etcd3metrics.RecordDecodeError(badGr) }},
	}
	for _, c := range cases {
		r := panics(c.f)
		t.Logf("%-40s panic: %v", c.name, r)
		if (r == nil) != strings.HasPrefix(c.name, "ok") {
			t.Errorf("%s: unexpected outcome %v", c.name, r)
		}
	}
}
