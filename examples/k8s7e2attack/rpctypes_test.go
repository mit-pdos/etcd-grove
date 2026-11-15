package k8s7e2attack

import (
	"reflect"
	"testing"

	"go.etcd.io/etcd/api/v3/v3rpc/rpctypes"
)

// TestRpctypesErrTypes probes the restated rpctypes initializer axioms (ErrCompacted_init,
// ErrFutureRev_init, rpctypesInit; k8s 7e-2's D1): the two globals hold rpctypes.EtcdError values,
// so `err == ErrCompacted` compares comparable structs and errors.Is may take them as an EtcdError
// target.
func TestRpctypesErrTypes(t *testing.T) {
	want := reflect.TypeOf(rpctypes.EtcdError{})
	for name, e := range map[string]error{
		"ErrCompacted": rpctypes.ErrCompacted, "ErrFutureRev": rpctypes.ErrFutureRev,
	} {
		if got := reflect.TypeOf(e); got != want {
			t.Fatalf("%s: dynamic type %v, want %v", name, got, want)
		}
		if !reflect.TypeOf(e).Comparable() {
			t.Fatalf("%s: not comparable", name)
		}
	}
}
