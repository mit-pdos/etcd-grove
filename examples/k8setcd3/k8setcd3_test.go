package k8setcd3

import (
	"os"
	"testing"

	"github.com/anishathalye/porcupine"
)

// TestMain runs the driver: the store's history is linearizable under Model (Main panics
// otherwise), and the run reaches the check.
func TestMainLinearizable(t *testing.T) {
	os.RemoveAll("k8setcd3.etcd")
	defer os.RemoveAll("k8setcd3.etcd")
	r := Main(4, 60)
	if r != porcupine.Ok {
		t.Fatalf("Main: %v, want Ok", r)
	}
}

// The model's answers on the seeded store: a no-op update of a non-canonical item rewrites it
// (D30g), a no-op update of a canonical one does not.
func TestModelNoopRewrite(t *testing.T) {
	st := mstore{rv: 1}
	st = mstore{items: setItem(st.items, item{key: "a", obj: Obj{Name: "a", Value: "x", ResourceVersion: 2}, canon: false}), rv: 2}
	st1, o1 := mstep(Input{Kind: KUpdate, Key: "a", NoOp: true}, st)
	if st1.rv != 3 || o1.RV != 3 || o1.Value != "x" {
		t.Fatalf("no-op on non-canonical: %+v %+v", st1, o1)
	}
	st2, o2 := mstep(Input{Kind: KUpdate, Key: "a", NoOp: true}, st1)
	if st2.rv != 3 || o2.RV != 3 {
		t.Fatalf("no-op on canonical: %+v %+v", st2, o2)
	}
	_, o3 := mstep(Input{Kind: KDelete, Key: "a", Reject: "x"}, st2)
	if o3.Err != ERejected {
		t.Fatalf("rejected delete: %+v", o3)
	}
	_, o4 := mstep(Input{Kind: KGet, Key: "c"}, st2)
	if o4.Err != ENotFound || o4.ErrKey != "/registry/objs/c" || o4.ErrRV != 3 {
		t.Fatalf("missing get: %+v", o4)
	}
}
