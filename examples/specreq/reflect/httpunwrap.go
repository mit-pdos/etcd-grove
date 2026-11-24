package reflect

// net/http's reflection on readers and transports.
//
// Mirrors Go 1.27.3's net/http:
//   - transfer.go:1136-1150 (unwrapNopCloser): the reader's dynamic type is
//     compared with the types of io.NopCloser's two results, computed at
//     package init; then reflect.ValueOf(r).Field(0).Interface().(io.Reader)
//     takes the wrapped reader out of io's unexported struct. Used by
//     transferWriter to decide whether a request body is known to be empty.
//   - client.go:343: reflect.TypeOf(rt).String() == "*http2.Transport", a
//     test on a type's printed name.
//   - transport.go:452: reflect.ValueOf(altProto["https"]) is a struct with one
//     field, which is read with Field(0).Interface().
//
// To prove: Field(0) is called only on a struct value (Field panics on any
// other kind), Interface succeeds (it panics on a value read through an
// unexported field: io.nopCloser's field is the embedded exported Reader),
// and the type assertion to io.Reader succeeds. All follow from the type
// equality test, which relates the dynamic type of r to a type declared,
// unexported, in another package (io), except the last, which needs a
// premise: the wrapped reader is not nil. On io.NopCloser(nil), Field(0) is
// a nil interface and `.(io.Reader)` panics (a first draft of this snippet
// tried it). net/http reaches it from a Request whose Body is
// io.NopCloser(nil) with a nonzero ContentLength (transfer.go:107); reading
// that body would panic anyway, so it is a caller's precondition, not a bug,
// and a spec of unwrapNopCloser must state it.
//
// Needs R1 (type identity, including of another package's unexported types;
// a type's String) and R2 (ValueOf, Kind, NumField, Field, Interface with its
// read-only flag).

import (
	"bytes"
	"io"
	"net/http"
	"reflect"
	"strings"
)

var nopCloserType = reflect.TypeOf(io.NopCloser(nil))
var nopCloserWriterToType = reflect.TypeOf(io.NopCloser(struct {
	io.Reader
	io.WriterTo
}{}))

func unwrapNopCloser(r io.Reader) (underlyingReader io.Reader, isNopCloser bool) {
	switch reflect.TypeOf(r) {
	case nopCloserType, nopCloserWriterToType:
		return reflect.ValueOf(r).Field(0).Interface().(io.Reader), true
	default:
		return nil, false
	}
}

// isKnownInMemoryReader is transfer.go:1155.
func isKnownInMemoryReader(r io.Reader) bool {
	switch r.(type) {
	case *bytes.Reader, *bytes.Buffer, *strings.Reader:
		return true
	}
	if r, ok := unwrapNopCloser(r); ok {
		return isKnownInMemoryReader(r)
	}
	return false
}

// isHTTP2Transport is client.go:343's test.
func isHTTP2Transport(rt http.RoundTripper) bool {
	return reflect.TypeOf(rt).String() == "*http2.Transport"
}

// REQ reflect/http-unwrap: classifying a request body unwraps io.NopCloser by reflection
// without panicking (Field(0) on a struct, Interface on an exported field, the assertion to
// io.Reader), and sees through it to an in-memory reader; the transport-name test does not panic.
// Users: net/http's transferWriter (transfer.go:1136-1160, on every client request with a body);
// client.go:343 (on every Client.Do).
// Assumes: no body is io.NopCloser(nil) (unwrapNopCloser panics on it; so would reading it).
// Specs: none yet; needs R1 (identity of io's unexported types, String) and R2 (doc.go).
func ReqHTTPUnwrap() {
	if !isKnownInMemoryReader(io.NopCloser(strings.NewReader("x"))) { // nopCloserWriterTo
		panic("http-unwrap: strings.Reader not seen")
	}
	if isKnownInMemoryReader(io.NopCloser(io.LimitReader(strings.NewReader(""), 1))) { // nopCloser
		panic("http-unwrap: LimitReader is not in memory")
	}
	// a *http.Transport, as http.DefaultTransport is (not named here: the main tree's net/http
	// translation skips that variable, Code/net/http.toml, and goose refuses a reference to it)
	if isHTTP2Transport(&http.Transport{}) {
		panic("http-unwrap: a *http.Transport is not an HTTP/2 transport")
	}
}
