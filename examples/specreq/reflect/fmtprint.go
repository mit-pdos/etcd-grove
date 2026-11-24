package reflect

// fmt's %v, %+v and %#v of composite values: printValue's reflective walk.
//
// Mirrors Go 1.27.3 fmt/print.go: printArg (:697-751: basic types by a type
// switch, everything else `p.printValue(reflect.ValueOf(f), verb, 0)`),
// printValue (:756-919: by Kind; at depth > 0 the Stringer/error/Formatter
// methods are tried only if `value.CanInterface()`, so an unexported field's
// String method is never called; structs by NumField, with
// `Type().Field(i).Name` for %+v and %#v; a pointer at depth 0 to an array,
// slice, struct or map prints "&" and its pointee; any other pointer prints
// its address (fmtPointer, unsafedep.go); maps through internal/fmtsort,
// keys sorted), getField (:334-340: Field(i), and Elem of a non-nil
// interface). Users that print composites: raft util.go:120 (`%v` of
// []ReadState), raftpb/confstate.go:53 (`%+#v` of *ConfState), raft.go:784;
// etcdserver server.go:1448,1459,1842,1859,1869 (`%+v` of *Member,
// Attributes); bbolt internal/freelist/hashmap.go:185-291, array.go:78-94
// (%v of maps and []Pgid inside panics). Perennial models fmt by hand today.
//
// To prove: each Sprintf below returns exactly Go's string. (An address
// printed for a nested non-nil pointer depends on allocation: unsafedep.go.)
//
// Needs R1 (Kind, NumField, Field(i).Name, String of types for %#v) and R2
// (Field, Elem, IsNil, Len, Index, MapRange, CanInterface, Interface, the
// typed getters Int/Uint/String/Bool/Bytes) and fmtsort's comparison of
// keys by Kind.

import "fmt"

type ReadState struct {
	Index      uint64
	RequestCtx []byte
}

type Attributes struct {
	Name       string
	ClientURLs []string
}

type Member struct {
	ID uint64
	Attributes
	Next *Member
}

type upper string

func (u upper) String() string { return "U(" + string(u) + ")" }

type withStringers struct {
	Pub  upper
	priv upper
}

// REQ reflect/fmt-print: %v, %+v and %#v of structs, embedded structs, nil nested pointers, a
// pointer to a struct at depth 0, maps (keys sorted), slices, byte slices, and nested
// Stringers (called for an exported field, not for an unexported one) print as Go prints them.
// Users: raft util.go:120, raftpb/confstate.go:53, raft.go:784; etcdserver server.go:1448,1459,
// 1842,1859,1869; bbolt internal/freelist/hashmap.go:185-291, array.go:78-94.
// Assumes: nothing.
// Specs: none yet; needs R1, R2 and fmtsort (doc.go).
func ReqFmtPrint() {
	rs := []ReadState{{Index: 5, RequestCtx: []byte("a")}}
	if s := fmt.Sprintf("%v", rs); s != "[{5 [97]}]" {
		panic("fmt-print: %v of []ReadState: " + s)
	}
	m := &Member{ID: 1, Attributes: Attributes{Name: "n", ClientURLs: []string{"u"}}}
	if s := fmt.Sprintf("%+v", m); s != "&{ID:1 Attributes:{Name:n ClientURLs:[u]} Next:<nil>}" {
		panic("fmt-print: %+v of *Member: " + s)
	}
	if s := fmt.Sprintf("%v", m.Attributes); s != "{n [u]}" {
		panic("fmt-print: %v of a struct: " + s)
	}
	if s := fmt.Sprintf("%#v", Attributes{Name: "n"}); s != `reflect.Attributes{Name:"n", ClientURLs:[]string(nil)}` {
		panic("fmt-print: %#v: " + s)
	}
	if s := fmt.Sprintf("%v", map[Pgid]struct{}{9: {}, 3: {}, 5: {}}); s != "map[3:{} 5:{} 9:{}]" {
		panic("fmt-print: a map's keys are sorted: " + s)
	}
	if s := fmt.Sprintf("%v", map[string]int{"b": 2, "a": 1}); s != "map[a:1 b:2]" {
		panic("fmt-print: string keys: " + s)
	}
	if s := fmt.Sprintf("%v %s %d", []Pgid{4, 2}, []byte("hi"), []int{1}); s != "[4 2] hi [1]" {
		panic("fmt-print: slices: " + s)
	}
	if s := fmt.Sprintf("%v", withStringers{Pub: "a", priv: "b"}); s != "{U(a) b}" {
		panic("fmt-print: Stringers of exported fields only: " + s)
	}
	var nilMember *Member
	if s := fmt.Sprintf("%v %+v", nilMember, nil); s != "<nil> <nil>" {
		panic("fmt-print: nil: " + s)
	}
}
