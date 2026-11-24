package reflect

// Kind dispatch and the typed-nil test: reflect.ValueOf(x).IsNil() on an
// interface holding a nil pointer.
//
// Mirrors:
//   - go.etcd.io/etcd/server/v3@edc800c6f (upamanyus/etcd)
//     etcdserver/txn/util.go:105-106 (`func isNil(msg proto.Message) bool {
//     return msg == nil || reflect.ValueOf(msg).IsNil() }`), called by
//     WarnOfExpensiveRequest (:34), WarnOfFailedRequest (:42) and the
//     read-only warnings (:61, :85) before proto.Size; the response is a nil
//     *pb.RangeResponse or *pb.TxnResponse in an interface when the request
//     failed (apply/uber_applier.go:99,101, v3_server.go:127,360). Translated
//     with its body (Code/go_etcd_io/etcd/server/v3/etcdserver/txn.lean,
//     isNil).
//   - k8s.io/apimachinery@v0.0.0-20261021173754-0b7d352f711c/pkg/conversion/
//     helper.go:27-37 (EnforcePtr: Kind Pointer, Invalid for a nil interface,
//     IsNil, then Elem), which the apiserver's store calls on every list.
//   - go.uber.org/zap@v1.28.0 zapcore/field.go:214-231 (encodeStringer) and
//     zapcore/error.go:48-80 (encodeError): a recovered panic of a typed nil
//     prints "<nil>", tested by `v := reflect.ValueOf(stringer); v.Kind() ==
//     reflect.Ptr && v.IsNil()`. The same test in Go 1.27.3 fmt/print.go:585
//     (catchPanic) and log/slog/handler.go:592.
//
// Go's panics: IsNil on the zero Value (ValueOf of a nil interface) panics
// "reflect: call of reflect.Value.IsNil on zero Value"; on a non-nillable
// kind (a struct, an int) "reflect: call of reflect.Value.IsNil on struct
// Value". etcd's isNil is safe because `msg == nil` comes first and every
// proto.Message is a pointer; etcdmain/grpc_proxy_logger.go:79 has no such
// guard (MustPanicIsNilZeroValue is its shape; etcdmain is not translated).
//
// To prove: ReqTypedNil does not panic (IsNil is called only on a
// pointer-kinded or interface-held pointer value) and isNil is true exactly
// of a nil interface and of a nil pointer of any type; the Must* functions
// panic, with Go's message, and never return.
//
// Needs R2 (ValueOf, Kind of an interface-held value and of the zero Value,
// IsNil, Elem) and R1 (Kind of a type).

import "reflect"

// Message stands for proto.Message: every implementation is a pointer.
type Message interface{ ProtoReflect() any }

type RangeResponse2 struct{ Count int64 }

func (r *RangeResponse2) ProtoReflect() any { return r }

// isNil is etcdserver/txn/util.go:105.
func isNil(msg Message) bool {
	return msg == nil || reflect.ValueOf(msg).IsNil()
}

var errNotPointer = "expected pointer"

// enforcePtr is conversion.EnforcePtr (helper.go:27-37), with its errors as strings.
func enforcePtr(obj any) (reflect.Value, string) {
	v := reflect.ValueOf(obj)
	if v.Kind() != reflect.Pointer {
		if v.Kind() == reflect.Invalid {
			return reflect.Value{}, "expected pointer, but got invalid kind"
		}
		return reflect.Value{}, errNotPointer + ", but got " + v.Type().String() + " type"
	}
	if v.IsNil() {
		return reflect.Value{}, "expected pointer, but got nil"
	}
	return v.Elem(), ""
}

// typedNilString is the recover branch of zap's encodeStringer: a typed nil prints "<nil>".
func typedNilString(stringer any) (string, bool) {
	if v := reflect.ValueOf(stringer); v.Kind() == reflect.Pointer && v.IsNil() {
		return "<nil>", true
	}
	return "", false
}

// REQ reflect/typed-nil: isNil is true of a nil interface and of an interface holding a nil
// pointer, false of a non-nil pointer, without panicking; EnforcePtr returns the pointee of a
// non-nil pointer and an error (no panic) for a nil interface, a nil pointer and a non-pointer;
// zap's typed-nil test recognizes a nil pointer behind an interface.
// Users: etcd server/v3 etcdserver/txn/util.go:34,42,61,85,105; apiserver storage/etcd3
// GetList via conversion.EnforcePtr; zapcore/field.go:222, zapcore/error.go:55; fmt print.go:585.
// Assumes: nothing.
// Specs: none yet; needs R2 (ValueOf, Kind, IsNil, Elem) (doc.go).
func ReqTypedNil() {
	var resp *RangeResponse2
	if !isNil(nil) || !isNil(resp) || isNil(&RangeResponse2{}) {
		panic("typed-nil: isNil")
	}
	if v, err := enforcePtr(&RangeResponse2{Count: 3}); err != "" || v.Kind() != reflect.Struct || v.Field(0).Int() != 3 {
		panic("typed-nil: EnforcePtr of a pointer")
	}
	if _, err := enforcePtr(nil); err != "expected pointer, but got invalid kind" {
		panic("typed-nil: EnforcePtr of nil")
	}
	if _, err := enforcePtr(resp); err != "expected pointer, but got nil" {
		panic("typed-nil: EnforcePtr of a nil pointer")
	}
	if _, err := enforcePtr(RangeResponse2{}); err != "expected pointer, but got reflect.RangeResponse2 type" {
		panic("typed-nil: EnforcePtr of a struct")
	}
	if s, ok := typedNilString(resp); !ok || s != "<nil>" {
		panic("typed-nil: zap's typed-nil test")
	}
	if _, ok := typedNilString(3); ok {
		panic("typed-nil: an int is not a typed nil")
	}
}

// REQ reflect/typed-nil (panics): IsNil of the zero Value (ValueOf of a nil interface) panics
// "reflect: call of reflect.Value.IsNil on zero Value": the semantics must not return here.
// Users: the shape of etcd's etcdmain/grpc_proxy_logger.go:79 (not translated).
// Specs: none yet.
func MustPanicIsNilZeroValue() bool {
	var msg Message
	return reflect.ValueOf(msg).IsNil()
}

// REQ reflect/typed-nil (panics): IsNil of a struct value panics "reflect: call of
// reflect.Value.IsNil on struct Value".
// Specs: none yet.
func MustPanicIsNilStruct() bool {
	return reflect.ValueOf(RangeResponse2{}).IsNil()
}
