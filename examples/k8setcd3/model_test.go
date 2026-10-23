package k8setcd3

import (
	"context"
	"strconv"
	"testing"

	metav1 "k8s.io/apimachinery/pkg/apis/meta/v1"
	"k8s.io/apimachinery/pkg/runtime"
	"k8s.io/apiserver/pkg/storage"
	"k8s.io/apiserver/pkg/storage/testing/correctness"
)

// TObj is the driver's object as a Kubernetes object (an ObjectMeta), for the real Model.
type TObj struct {
	metav1.TypeMeta
	metav1.ObjectMeta
	Value string
}

func (o *TObj) DeepCopyObject() runtime.Object {
	c := *o
	c.ObjectMeta = *o.ObjectMeta.DeepCopy()
	return &c
}

func newTObj() runtime.Object { return &TObj{} }

// The test's callbacks on TObj, as the driver's on Obj.
func tValidateFor(reject string) storage.ValidateObjectFunc {
	return func(ctx context.Context, obj runtime.Object) error {
		o := obj.(*TObj)
		if reject != "" && o.Value == reject {
			return errDeleteRejected
		}
		return nil
	}
}

func tTryUpdateFor(in Input) storage.UpdateFunc {
	return func(input runtime.Object, res storage.ResponseMeta) (runtime.Object, *uint64, error) {
		o := input.(*TObj)
		if in.Reject != "" && o.Value == in.Reject {
			return nil, nil, errUpdateRejected
		}
		c := o.DeepCopyObject().(*TObj)
		if !in.NoOp {
			c.Value = in.Val
		}
		return c, nil, nil
	}
}

// decRV is a resource version as Kubernetes' objects keep it (decimal, empty for 0).
func decRV(rv uint64) string {
	if rv == 0 {
		return ""
	}
	return strconv.FormatUint(rv, 10)
}

// request is an Input as the real Model's request.
func request(in Input) correctness.Request {
	key := storeKey(in.Key)
	switch in.Kind {
	case KCreate:
		return correctness.Request{Op: correctness.OpCreate, Key: key,
			Create: correctness.CreateRequest{Object: &TObj{ObjectMeta: metav1.ObjectMeta{Name: in.Key}, Value: in.Val}}}
	case KDelete:
		return correctness.Request{Op: correctness.OpDelete, Key: key,
			Delete: correctness.DeleteRequest{ValidateDeletion: tValidateFor(in.Reject)}}
	case KUpdate:
		return correctness.Request{Op: correctness.OpUpdate, Key: key,
			Update: correctness.UpdateRequest{UpdateFunc: tTryUpdateFor(in)}}
	default:
		return correctness.Request{Op: correctness.OpGet, Key: key,
			Get: correctness.GetRequest{Options: storage.GetOptions{IgnoreNotFound: in.IgnoreNotFound}}}
	}
}

// response is an Output as the real Model's response.
func response(in Input, out Output) correctness.Response {
	switch out.Err {
	case ENotFound:
		return correctness.Response{Err: storage.NewKeyNotFoundError(out.ErrKey, out.ErrRV)}
	case EExists:
		return correctness.Response{Err: storage.NewKeyExistsError(out.ErrKey, out.ErrRV)}
	case ERejected:
		if in.Kind == KDelete {
			return correctness.Response{Err: errDeleteRejected}
		}
		return correctness.Response{Err: errUpdateRejected}
	}
	if out.Name == "" && out.Value == "" && out.RV == 0 {
		return correctness.Response{Object: &TObj{}}
	}
	return correctness.Response{Object: &TObj{
		ObjectMeta: metav1.ObjectMeta{Name: out.Name, ResourceVersion: decRV(out.RV)}, Value: out.Value}}
}

// TestModelMatchesCorrectnessModel runs random traffic from the empty store through the driver's
// Model and the real correctness.Model at once: on every operation the real Model accepts the
// driver's model's answer, and both reach the same state. (From the empty store every item is
// canonical, where the D30g fix does not change the Model.)
func TestModelMatchesCorrectnessModel(t *testing.T) {
	for run := 0; run < 200; run++ {
		real := correctness.NewEmptyModel(Prefix, newTObj, nil, storage.APIObjectVersioner{})
		st := mstore{rv: 1}
		for i := 0; i < 60; i++ {
			in := Gen(0).(Input)
			next, out := mstep(in, st)
			ok, rnext, _ := real.Step(request(in), response(in, out))
			if !ok {
				t.Fatalf("run %d op %d %+v: the real Model rejects %+v", run, i, in, out)
			}
			// a wrong answer is rejected (the resource version off by one)
			if out.Err == ENone && out.RV != 0 && in.Kind != KGet {
				bad := out
				bad.RV = next.rv + 1
				if ok, _, _ := real.Step(request(in), response(in, bad)); ok {
					t.Fatalf("run %d op %d: the real Model accepts a wrong answer", run, i)
				}
			}
			real = rnext
			st = next
			if real.ResourceVersion != st.rv || len(real.Items) != len(st.items) {
				t.Fatalf("run %d op %d: states differ: %d/%d items, rv %d/%d", run, i,
					len(real.Items), len(st.items), real.ResourceVersion, st.rv)
			}
			for _, it := range st.items {
				ro, ok := real.Items[storeKey(it.key)].(*TObj)
				if !ok || ro.Name != it.obj.Name || ro.Value != it.obj.Value ||
					ro.ResourceVersion != decRV(it.obj.ResourceVersion) {
					t.Fatalf("run %d op %d: item %s differs: %+v vs %+v", run, i, it.key, ro, it.obj)
				}
			}
		}
	}
}

// TestModelNonCanonicalDiffers: on a non-canonical item a no-op update rewrites (the store does),
// which the unfixed real Model rejects (issues/k8s-correctness-model-noop-rewrite.md).
func TestModelNonCanonicalDiffers(t *testing.T) {
	st := mstore{items: []item{{key: "a", obj: Obj{Name: "a", Value: "x", ResourceVersion: 2}, canon: false}}, rv: 2}
	in := Input{Kind: KUpdate, Key: "a", NoOp: true}
	_, out := mstep(in, st)
	real := correctness.NewEmptyModel(Prefix, newTObj, nil, storage.APIObjectVersioner{})
	real.ResourceVersion = 2
	real.Items[storeKey("a")] = &TObj{ObjectMeta: metav1.ObjectMeta{Name: "a", ResourceVersion: "2"}, Value: "x"}
	if ok, _, _ := real.Step(request(in), response(in, out)); ok {
		t.Fatalf("the unfixed Model accepts the rewrite %+v", out)
	}
}
