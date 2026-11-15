package registry

import (
	"testing"

	apierrors "k8s.io/apimachinery/pkg/api/errors"
	metainternalversion "k8s.io/apimachinery/pkg/apis/meta/internalversion"
	metainternalversionvalidation "k8s.io/apimachinery/pkg/apis/meta/internalversion/validation"
	metav1 "k8s.io/apimachinery/pkg/apis/meta/v1"
	"k8s.io/apiserver/pkg/apis/example"
	genericapirequest "k8s.io/apiserver/pkg/endpoints/request"
	"k8s.io/apiserver/pkg/features"
	"k8s.io/apiserver/pkg/storage"
	utilfeature "k8s.io/apiserver/pkg/util/feature"
	featuregatetesting "k8s.io/component-base/featuregate/testing"
)

// TestListResourceVersionAboveInt64 lists through the registry's Store, backed by the etcd3
// storage without the watch cache, with a resource version above the current revision. Below
// 2^63 the list fails with a too-large resource version error; at or above 2^63 it succeeds and
// returns the current objects labelled with the requested resource version.
func TestListResourceVersionAboveInt64(t *testing.T) {
	for _, stream := range []bool{true, false} {
		t.Run(map[bool]string{true: "RangeStream", false: "paginated"}[stream], func(t *testing.T) {
			featuregatetesting.SetFeatureGateDuringTest(t, utilfeature.DefaultFeatureGate, features.EtcdRangeStream, stream)
			testListResourceVersionAboveInt64(t)
		})
	}
}

func testListResourceVersionAboveInt64(t *testing.T) {
	ctx := genericapirequest.WithNamespace(genericapirequest.NewContext(), "test")
	destroy, registry := newTestGenericStoreRegistry(t, scheme, false)
	defer destroy()

	pod := &example.Pod{ObjectMeta: metav1.ObjectMeta{Namespace: "test", Name: "foo"}}
	if _, err := registry.Create(ctx, pod, nil, &metav1.CreateOptions{}); err != nil {
		t.Fatalf("create: %v", err)
	}

	for _, tc := range []struct {
		name  string
		opts  metainternalversion.ListOptions
	}{
		{"exact, 10^6", metainternalversion.ListOptions{ResourceVersion: "1000000", ResourceVersionMatch: metav1.ResourceVersionMatchExact}},
		{"exact, 2^64-1", metainternalversion.ListOptions{ResourceVersion: "18446744073709551615", ResourceVersionMatch: metav1.ResourceVersionMatchExact}},
		{"exact, 2^63", metainternalversion.ListOptions{ResourceVersion: "9223372036854775808", ResourceVersionMatch: metav1.ResourceVersionMatchExact}},
		{"legacy with limit, 2^64-1", metainternalversion.ListOptions{ResourceVersion: "18446744073709551615", Limit: 5}},
	} {
		t.Run(tc.name, func(t *testing.T) {
			opts := tc.opts
			// What the list handler checks before calling the registry (handlers.ListResource).
			if errs := metainternalversionvalidation.ValidateListOptions(&opts, false); len(errs) > 0 {
				t.Fatalf("rejected by validation: %v", errs)
			}
			obj, err := registry.List(ctx, &opts)
			if err == nil {
				l := obj.(*example.PodList)
				t.Errorf("resourceVersion=%s: expected a too-large resource version error, got %d items at resourceVersion %q",
					opts.ResourceVersion, len(l.Items), l.ResourceVersion)
				return
			}
			if !storage.IsTooLargeResourceVersion(err) && !apierrors.IsTimeout(err) {
				t.Errorf("resourceVersion=%s: expected a too-large resource version error, got %v", opts.ResourceVersion, err)
			}
		})
	}
}
