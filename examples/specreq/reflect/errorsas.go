package reflect

// errors.As, as grpc's status.FromError uses it.
//
// Mirrors google.golang.org/grpc@v1.84.0/status/status.go (FromError:
// `var grpcstatus interface{ GRPCStatus() *Status }; if errors.As(err,
// &grpcstatus) { ... }`) and Go 1.27.3's errors/wrap.go (As). As works through
// internal/reflectlite: it panics "errors: target cannot be nil", "errors:
// target must be a non-nil pointer" and "errors: *target must be interface or
// implement error", then walks the Unwrap chain (both Unwrap() error and
// Unwrap() []error), testing reflectlite.TypeOf(err).AssignableTo(targetType)
// and storing with reflectlite.ValueOf(target).Elem().Set(ValueOf(err)).
// etcd calls errors.As and errors.Is throughout (client/v3's
// rpctypes.Error, the server's ErrGRPC* mapping); this repository has
// axioms for the shapes it needed (errors.AsLeafTy, errors.IsStatusErr, ...).
//
// To prove: As does not panic (every target is a non-nil pointer to an
// interface or to an error type) and, when it returns true, *target holds the
// error of the chain it matched. A spec over the chain: As(err, &t) with t of
// interface type I is true iff some error of the chain has a dynamic type
// implementing I.
//
// Needs R1 (TypeOf, Kind, Elem, Implements, AssignableTo over interface and
// concrete types) and R2 (ValueOf, Elem, Set of an interface-typed cell) —
// here on errors' own reflectlite, which Perennial models by hand today.

import (
	"errors"
	"fmt"
)

type Status struct {
	Code int
	Msg  string
}

type statusError struct{ s *Status }

func (e *statusError) Error() string       { return e.s.Msg }
func (e *statusError) GRPCStatus() *Status { return e.s }

// FromError is status.FromError, minimized.
func FromError(err error) (*Status, bool) {
	if err == nil {
		return nil, true
	}
	var grpcstatus interface{ GRPCStatus() *Status }
	if errors.As(err, &grpcstatus) {
		return grpcstatus.GRPCStatus(), true
	}
	return &Status{Code: 2, Msg: err.Error()}, false // codes.Unknown
}

// REQ reflect/errors-as: status.FromError finds a gRPC status through fmt's %w wrapping and
// through errors.Join (As does not panic on its interface-typed target, and stores the matched
// error), and As with a concrete pointer target stores the same error.
// Users: grpc@v1.84.0/status/status.go (FromError, on every RPC error); etcd's
// rpctypes.Error/ErrGRPC* mapping and client/v3's retry decisions.
// Assumes: nothing.
// Specs: none yet; needs R1 (Implements, AssignableTo) and R2 (Elem, Set), on errors'
// reflectlite (doc.go).
func ReqErrorsAs() {
	base := &statusError{s: &Status{Code: 5, Msg: "not found"}}
	if s, ok := FromError(fmt.Errorf("range: %w", base)); !ok || s != base.s {
		panic("errors-as: status lost through %w")
	}
	if s, ok := FromError(errors.Join(errors.New("other"), base)); !ok || s != base.s {
		panic("errors-as: status lost through Join")
	}
	var se *statusError
	if !errors.As(fmt.Errorf("x: %w", base), &se) || se != base {
		panic("errors-as: concrete target")
	}
}
