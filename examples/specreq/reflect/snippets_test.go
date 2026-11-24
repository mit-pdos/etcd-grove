package reflect

import (
	"encoding/json"
	"net/rpc"
	"runtime"
	"strings"
	"testing"
)

// TestSnippets runs every snippet: each panics if what its users rely on fails.
func TestSnippets(t *testing.T) {
	ReqStructTags()
	ReqRegisterService()
	ReqHTTPUnwrap()
	ReqErrorsAs()
	ReqTypeIdentity()
	ReqTypedNil()
	ReqPtrSet()
	ReqListItems()
	ReqErrorsIsComparable()
	ReqDeepEqual()
	ReqSortSlice()
	ReqBinaryRW()
	ReqFmtPrint()
	ReqUnexported()
	ReqJSONWalk()
	ReqRPCRegister()
	ReqTypeConstruct()
	ReqConvert()
	ReqPBFields()
	ReqCmpWalk()
	ReqUnsafePointerIdentity()
	ReqUnsafeNewAt()
}

// mustPanic checks that f panics with a message containing want: the Must* snippets are
// where Go panics, and a semantics must not let them return.
func mustPanic(t *testing.T, name, want string, f func()) {
	t.Helper()
	defer func() {
		r := recover()
		if r == nil {
			t.Fatalf("%s: returned; Go panics with %q", name, want)
		}
		var msg string
		switch e := r.(type) {
		case error:
			msg = e.Error()
		case string:
			msg = e
		default:
			t.Fatalf("%s: panicked with %T %v", name, r, r)
		}
		if !strings.Contains(msg, want) {
			t.Fatalf("%s: panicked with %q, want %q", name, msg, want)
		}
	}()
	f()
}

// TestPanics checks that every Must* snippet panics, with Go's message.
func TestPanics(t *testing.T) {
	mustPanic(t, "MustPanicIsNilZeroValue", "reflect: call of reflect.Value.IsNil on zero Value",
		func() { MustPanicIsNilZeroValue() })
	mustPanic(t, "MustPanicIsNilStruct", "reflect: call of reflect.Value.IsNil on struct Value",
		func() { MustPanicIsNilStruct() })
	mustPanic(t, "MustPanicSetUnaddressable", "reflect: reflect.Value.Set using unaddressable value",
		MustPanicSetUnaddressable)
	mustPanic(t, "MustPanicSetWrongType", "reflect.Set: value of type *reflect.Pod2 is not assignable to type reflect.Pod2",
		MustPanicSetWrongType)
	mustPanic(t, "MustPanicAppendWrongElem", "reflect.Set: value of type *reflect.Pod2 is not assignable to type reflect.Pod2",
		MustPanicAppendWrongElem)
	mustPanic(t, "MustPanicContextKeyNotComparable", "key is not comparable",
		func() { MustPanicContextKeyNotComparable() })
	mustPanic(t, "MustPanicSortNotSlice", "reflect: call of Swapper on int Value",
		MustPanicSortNotSlice)
	mustPanic(t, "MustPanicBinaryReadUnexported", "reflect: reflect.Value.SetUint using value obtained using unexported field",
		MustPanicBinaryReadUnexported)
	mustPanic(t, "MustPanicInterfaceUnexported", "reflect.Value.Interface: cannot return value obtained from unexported field or method",
		func() { MustPanicInterfaceUnexported() })
	mustPanic(t, "MustPanicSetUnexported", "reflect: reflect.Value.SetString using value obtained using unexported field",
		MustPanicSetUnexported)
	mustPanic(t, "MustPanicRegisterNil", "reflect: call of reflect.Value.Type on zero Value",
		MustPanicRegisterNil)
	mustPanic(t, "MustPanicConvertMismatch", "invalid type: got reflect.Number, want reflect.EntryType",
		func() { MustPanicConvertMismatch() })
	mustPanic(t, "MustPanicConvertString", "reflect.Value.Convert: value of type string cannot be converted to type reflect.EntryType",
		func() { MustPanicConvertString() })
	mustPanic(t, "MustPanicCmpUnexported", "cannot handle unexported field at .cache",
		func() { MustPanicCmpUnexported() })
}

// TestMirrors checks the minimized copies against the libraries they mirror: jsonwalk.go's
// marshal against encoding/json, rpcregister.go's register against net/rpc's Register.
func TestMirrors(t *testing.T) {
	m := MemberRecord{ID: 7, RaftAttributes: RaftAttributes{PeerURLs: []string{"http://a:2380"}},
		Labels: map[string]string{"b": "2", "a": "1"}, Peer: Peer{Host: "h"}, Ignored: "x", secret: "s"}
	for _, x := range []any{m, &m, (*MemberRecord)(nil), URLs(nil), URLs{}, RaftAttributes{IsLearner: true}} {
		want, err := json.Marshal(x)
		if err != nil {
			t.Fatal(err)
		}
		if got := marshal(x); got != string(want) {
			t.Errorf("marshal(%#v) = %s, encoding/json gives %s", x, got, want)
		}
	}
	var out *MemberRecord
	if err := json.Unmarshal([]byte(memberJSONValue), &out); err != nil || out.ID != 7 || len(out.Labels) != 2 {
		t.Errorf("encoding/json decodes the record differently: %v %+v", err, out)
	}
	var nonPointer, nilTarget any = MemberRecord{}, nil
	if err := json.Unmarshal([]byte(memberJSON), nonPointer); err == nil ||
		err.Error() != "json: Unmarshal(non-pointer reflect.MemberRecord)" {
		t.Errorf("encoding/json's error for a non-pointer: %v", err)
	}
	if err := json.Unmarshal([]byte(memberJSON), nilTarget); err == nil || err.Error() != "json: Unmarshal(nil)" {
		t.Errorf("encoding/json's error for nil: %v", err)
	}
	for _, c := range []struct {
		rcvr any
		ok   bool
	}{{new(Arith), true}, {Arith(0), false}, {&noMethods{}, false}, {&Pod2{}, false}} {
		_, mine := register(c.rcvr)
		err := rpc.NewServer().Register(c.rcvr)
		if (mine == "") != c.ok || (err == nil) != c.ok || (err != nil && err.Error() != mine) {
			t.Errorf("register(%T): mirror %q, net/rpc %v", c.rcvr, mine, err)
		}
	}
	if fn := runtime.FuncForPC(funcPC(someHandler)); fn == nil || fn.Name() != pkgPath+".someHandler" {
		t.Errorf("FuncForPC of funcPC(someHandler): %v", fn)
	}
	mustPanic(t, "net/rpc Register(nil)", "reflect: call of reflect.Value.Type on zero Value",
		func() { _ = rpc.NewServer().Register(nil) })
}
