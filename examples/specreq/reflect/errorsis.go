package reflect

// Comparability by reflection: errors.Is compares with == only when the
// target's type is comparable, and context.WithValue refuses an
// uncomparable key.
//
// Mirrors Go 1.27.3 errors/wrap.go:44-70 (Is: `isComparable :=
// reflectlite.TypeOf(target).Comparable()`, then `if isComparable && err ==
// target`, then the error's own Is method, then Unwrap() error and Unwrap()
// []error) and context/context.go:727-740 (WithValue: panics "cannot create
// context from nil parent", "nil key", "key is not comparable" when
// `!reflectlite.TypeOf(key).Comparable()`). errors.Is is how etcd's client
// and server classify errors (client/v3's isHaltErr/isUnavailableErr,
// rpctypes.ErrGRPC*, `errors.Is(err, context.Canceled)` throughout);
// WithValue carries grpc's metadata and etcd's request ids.
//
// Go's panics: comparing two interfaces whose dynamic type is not comparable
// panics "runtime error: comparing uncomparable type ..."; Is avoids it by
// the Comparable test (MultiErr below is a slice type: `err == target` would
// panic); WithValue panics on a slice key.
//
// To prove: Is never panics, is true when an error of the Unwrap tree is ==
// the (comparable) target or says so by its Is method, and false otherwise,
// including for an uncomparable target that is not in the tree by its Is
// method; WithValue with a comparable key does not panic and Value finds it.
//
// Needs R1 (Comparable of a type, for interface-held dynamic types) on
// reflectlite.

import (
	"context"
	"errors"
	"fmt"
)

// MultiErr is an error of a slice type: not comparable.
type MultiErr []string

func (m MultiErr) Error() string { return fmt.Sprint([]string(m)) }

// codeErr is comparable; its Is method matches by code (as rpctypes.EtcdError's errors do by
// being the same value).
type codeErr struct{ code int }

func (e codeErr) Error() string { return fmt.Sprintf("code %d", e.code) }

var errCompacted = codeErr{code: 11}

type ctxKey struct{ name string }

// REQ reflect/errors-is: errors.Is finds a comparable target through %w and Join, does not
// panic on an uncomparable error or target (it skips ==), and context.WithValue accepts a
// comparable struct key whose Value is found again.
// Users: errors.Is throughout etcd's client and server (client/v3 retry and halt decisions,
// rpctypes); context.WithValue in grpc metadata and etcd's request contexts.
// Assumes: nothing.
// Specs: none yet; needs R1 (Comparable) on reflectlite (doc.go).
func ReqErrorsIsComparable() {
	if !errors.Is(fmt.Errorf("range: %w", errCompacted), errCompacted) {
		panic("errors-is: through %w")
	}
	if !errors.Is(errors.Join(errors.New("x"), errCompacted), codeErr{code: 11}) {
		panic("errors-is: through Join, by ==")
	}
	m := MultiErr{"a", "b"}
	if errors.Is(fmt.Errorf("w: %w", m), MultiErr{"a", "b"}) {
		panic("errors-is: an uncomparable target is never ==")
	}
	if errors.Is(m, errCompacted) {
		panic("errors-is: an uncomparable error in the chain")
	}
	ctx := context.WithValue(context.Background(), ctxKey{"rid"}, 7)
	if v, ok := ctx.Value(ctxKey{"rid"}).(int); !ok || v != 7 {
		panic("errors-is: WithValue of a comparable key")
	}
}

// REQ reflect/errors-is (panics): context.WithValue with a slice key panics "key is not
// comparable".
// Specs: none yet.
func MustPanicContextKeyNotComparable() context.Context {
	return context.WithValue(context.Background(), MultiErr{"k"}, 1)
}
