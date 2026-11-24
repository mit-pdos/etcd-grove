package reflect

// go-cmp's reflective walk (cmp.Diff, cmp.Equal), minimized.
//
// Mirrors github.com/google/go-cmp@v0.7.0 cmp/compare.go:
//   - :141-165 (the root: ValueOf of both, wrapped in an `any` when the
//     types differ);
//   - :271-299 (compareAny: by Kind; Bool, Int, Uint, String by value;
//     Pointer by IsNil and then Elem, through the cycle check; lib panic
//     "%v kind not handled");
//   - :312-321 (tryMethod: `t.MethodByName("Equal")`, of type func(T) bool,
//     then Call and Bool);
//   - :375-416 (compareStruct: NumField, Field(i); an unexported field
//     without an Exporter option panics, options.go:256: "cannot handle
//     unexported field at <path>");
//   - :510-550 (compareMap: IsNil, MapKeys sorted by internal/value/
//     sort.go:16-22, MapIndex of each key in both);
//   - :455-508 (compareSlice: Len, Index; the real one diffs by edit script).
// The cycle check (internal/value/pointer.go:20-23, `v.Pointer()`) and the
// Exporter's access (export.go:18-31, NewAt + UnsafeAddr) are
// unsafe-dependent (unsafedep.go). Users: etcd server/v3
// storage/backend/verify.go:108 (`cmp.Diff(dataFromWriteTxn,
// dataFromReadTxn)`, two map[string]string); the k8s checker
// examples/k8s/etcd3/correctness/replay.go:134 and WatchValidator.
// compareEvents (`cmp.Diff`, names-only: Code/github_com/google/go_cmp/
// cmp.toml, a trust-boundary axiom at the checker's types).
//
// To prove: diff is "" iff the values are equal by the walk (an Equal method
// decides for its type), lists the paths that differ, in key order for
// maps, and panics on an unexported field.
//
// Needs R1 (Kind, NumField, Field(i) with Name and IsExported, MethodByName
// with its func type, Key/Elem) and R2 (Field, Index, Len, MapKeys, MapIndex,
// IsNil, Elem, Method's Func Call, the typed getters).

import (
	"reflect"
	"sort"
	"strconv"
	"strings"
)

// Rev has an Equal method: go-cmp calls it instead of walking the struct.
type Rev struct {
	Main int64
	Sub  int64
}

func (r Rev) Equal(o Rev) bool { return r.Main == o.Main }

type Resp struct {
	Rev   Rev
	Items map[string]string
	List  []string
}

type cmpState struct{ diffs []string }

func (s *cmpState) report(path string) { s.diffs = append(s.diffs, path) }

func tryEqualMethod(vx, vy reflect.Value) (bool, bool) {
	m, ok := vx.Type().MethodByName("Equal")
	if !ok || m.Type.NumIn() != 2 || m.Type.In(1) != vx.Type() || m.Type.NumOut() != 1 || m.Type.Out(0).Kind() != reflect.Bool {
		return false, false
	}
	return m.Func.Call([]reflect.Value{vx, vy})[0].Bool(), true
}

func (s *cmpState) compareAny(path string, vx, vy reflect.Value) {
	if eq, ok := tryEqualMethod(vx, vy); ok {
		if !eq {
			s.report(path)
		}
		return
	}
	switch vx.Kind() {
	case reflect.Bool:
		if vx.Bool() != vy.Bool() {
			s.report(path)
		}
	case reflect.Int, reflect.Int64:
		if vx.Int() != vy.Int() {
			s.report(path)
		}
	case reflect.Uint64:
		if vx.Uint() != vy.Uint() {
			s.report(path)
		}
	case reflect.String:
		if vx.String() != vy.String() {
			s.report(path)
		}
	case reflect.Pointer:
		if vx.IsNil() || vy.IsNil() {
			if vx.IsNil() != vy.IsNil() {
				s.report(path)
			}
			return
		}
		s.compareAny("*"+path, vx.Elem(), vy.Elem())
	case reflect.Struct:
		t := vx.Type()
		for i := 0; i < t.NumField(); i++ {
			f := t.Field(i)
			if !f.IsExported() {
				panic("cannot handle unexported field at " + path + "." + f.Name)
			}
			s.compareAny(path+"."+f.Name, vx.Field(i), vy.Field(i))
		}
	case reflect.Slice:
		if vx.IsNil() != vy.IsNil() || vx.Len() != vy.Len() {
			s.report(path)
			return
		}
		for i := 0; i < vx.Len(); i++ {
			s.compareAny(path+"["+strconv.Itoa(i)+"]", vx.Index(i), vy.Index(i))
		}
	case reflect.Map:
		if vx.IsNil() != vy.IsNil() {
			s.report(path)
			return
		}
		keys := map[string]reflect.Value{}
		for _, k := range append(vx.MapKeys(), vy.MapKeys()...) {
			keys[k.String()] = k
		}
		var names []string
		for n := range keys {
			names = append(names, n)
		}
		sort.Strings(names)
		for _, n := range names {
			ex, ey := vx.MapIndex(keys[n]), vy.MapIndex(keys[n])
			if !ex.IsValid() || !ey.IsValid() {
				s.report(path + "[" + strconv.Quote(n) + "]")
				continue
			}
			s.compareAny(path+"["+strconv.Quote(n)+"]", ex, ey)
		}
	default:
		panic(vx.Kind().String() + " kind not handled")
	}
}

// diff is cmp.Diff's verdict, the report reduced to the differing paths.
func diff(x, y any) string {
	vx, vy := reflect.ValueOf(x), reflect.ValueOf(y)
	if vx.Type() != vy.Type() {
		return "{" + vx.Type().String() + "} != {" + vy.Type().String() + "}"
	}
	s := &cmpState{}
	s.compareAny("", vx, vy)
	return strings.Join(s.diffs, ",")
}

// REQ reflect/cmp-walk: diff of two equal map[string]string is "", of maps that differ lists
// the differing keys in order; a struct's Equal method decides for its type (Sub is ignored);
// nested slices and maps are walked; values of different types differ.
// Users: etcd storage/backend/verify.go:108; the k8s checker correctness/replay.go:134 and
// WatchValidator.compareEvents (names-only cmp.Diff).
// Assumes: nothing.
// Specs: none yet; needs R1 (MethodByName, fields) and R2 (Call, MapKeys, MapIndex) (doc.go).
func ReqCmpWalk() {
	w := map[string]string{"k1": "v1", "k2": "v2"}
	r := map[string]string{"k2": "v2", "k1": "v1"}
	if d := diff(w, r); d != "" {
		panic("cmp-walk: equal maps: " + d)
	}
	r["k1"] = "x"
	r["k0"] = "y"
	if d := diff(w, r); d != `["k0"],["k1"]` {
		panic("cmp-walk: differing keys: " + d)
	}
	a := Resp{Rev: Rev{Main: 3, Sub: 1}, Items: map[string]string{"a": "1"}, List: []string{"x"}}
	b := Resp{Rev: Rev{Main: 3, Sub: 2}, Items: map[string]string{"a": "1"}, List: []string{"x"}}
	if d := diff(&a, &b); d != "" {
		panic("cmp-walk: Equal method: " + d)
	}
	b.List = []string{"y"}
	b.Rev.Main = 4
	if d := diff(&a, &b); d != "*.Rev,*.List[0]" {
		panic("cmp-walk: nested: " + d)
	}
	if d := diff(1, int64(1)); d != "{int} != {int64}" {
		panic("cmp-walk: types: " + d)
	}
}

// REQ reflect/cmp-walk (panics): diff of structs with an unexported field panics "cannot
// handle unexported field at .cache" (go-cmp without AllowUnexported or an Exporter).
// Specs: none yet.
func MustPanicCmpUnexported() string {
	return diff(withUnexported{Name: "x"}, withUnexported{Name: "x"})
}
