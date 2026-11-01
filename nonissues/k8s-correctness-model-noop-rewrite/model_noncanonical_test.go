package etcd3

import (
	"testing"

	metav1 "k8s.io/apimachinery/pkg/apis/meta/v1"
	"k8s.io/apimachinery/pkg/runtime"
	"k8s.io/apiserver/pkg/apis/example"
	"k8s.io/apiserver/pkg/storage"
	storagetesting "k8s.io/apiserver/pkg/storage/testing"
	"k8s.io/apiserver/pkg/storage/testing/correctness"
	"k8s.io/apiserver/pkg/storage/value"
)

// The etcd3 store rewrites an object whose stored bytes are not what the codec would write now,
// or that the transformer reports stale, on a no-op update (as
// RunTestGuaranteedUpdateChecksStoredData requires): correctness.Model rejects that response,
// since it skips every update that leaves the object equal up to its resource version.
func TestModelRejectsRewriteOfNonCanonicalData(t *testing.T) {
	for _, tc := range []struct {
		name string
		// the transformer the object is created with (nil: the store's)
		seed value.Transformer
		// the transformer the update reads with (nil: the store's)
		read value.Transformer
	}{
		// stored in a form the codec does not write now (a leading space after the prefix,
		// as RunTestGuaranteedUpdateChecksStoredData seeds it)
		{"non-canonical bytes", storagetesting.NewPrefixTransformer([]byte(defaultTestPrefix+" "), false), nil},
		// the transformer reports the stored value stale (a key rotation)
		{"stale", nil, storagetesting.NewPrefixTransformer([]byte(defaultTestPrefix), true)},
	} {
		t.Run(tc.name, func(t *testing.T) {
			ctx, s, _ := testSetup(t)
			st := &storeWithPrefixTransformer{s}
			with := func(tr value.Transformer) func() {
				if tr == nil {
					return func() {}
				}
				return st.UpdatePrefixTransformer(func(*storagetesting.PrefixTransformer) value.Transformer { return tr })
			}
			versioner := storage.APIObjectVersioner{}
			rv, err := s.GetCurrentResourceVersion(ctx)
			if err != nil {
				t.Fatal(err)
			}
			model := correctness.NewEmptyModel("", func() runtime.Object { return &example.Pod{} },
				func() runtime.Object { return &example.PodList{} }, versioner)
			model.ResourceVersion = rv

			key := "/pods/test-ns/foo"
			input := &example.Pod{ObjectMeta: metav1.ObjectMeta{Name: "foo", Namespace: "test-ns"}}

			created := &example.Pod{}
			revert := with(tc.seed)
			err = s.Create(ctx, key, input.DeepCopy(), created, 0)
			revert()
			if err != nil {
				t.Fatal(err)
			}
			req := correctness.Request{Op: correctness.OpCreate, Key: key,
				Create: correctness.CreateRequest{Object: input.DeepCopy()}}
			ok, next, _ := model.Step(req, correctness.Response{Object: created})
			if !ok {
				t.Fatalf("model rejected the create: %+v", created)
			}
			model = next

			// A no-op update: tryUpdate returns its input unchanged.
			noop := func(obj runtime.Object, _ storage.ResponseMeta) (runtime.Object, *uint64, error) {
				return obj, nil, nil
			}
			out := &example.Pod{}
			revert = with(tc.read)
			err = s.GuaranteedUpdate(ctx, key, out, false, nil, noop, nil)
			revert()
			if err != nil {
				t.Fatal(err)
			}
			if out.ResourceVersion == created.ResourceVersion {
				t.Fatalf("store did not rewrite: %s", out.ResourceVersion)
			}
			t.Logf("store rewrote the object: RV %s -> %s", created.ResourceVersion, out.ResourceVersion)
			req = correctness.Request{Op: correctness.OpUpdate, Key: key,
				Update: correctness.UpdateRequest{UpdateFunc: noop}}
			ok, _, _ = model.Step(req, correctness.Response{Object: out})
			if ok {
				t.Fatalf("model accepted the rewrite")
			}
			t.Logf("correctness.Model rejects the store's response")
		})
	}
}
