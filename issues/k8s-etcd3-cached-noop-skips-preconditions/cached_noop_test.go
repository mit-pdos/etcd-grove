package etcd3

import (
	"testing"

	metav1 "k8s.io/apimachinery/pkg/apis/meta/v1"
	"k8s.io/apimachinery/pkg/runtime"
	"k8s.io/apiserver/pkg/apis/example"
	"k8s.io/apiserver/pkg/storage"
)

// TestGuaranteedUpdateCachedNoopChecksPreconditions: an update from a cached object that changes
// nothing must fail its resource version precondition when the object is no longer at that
// resource version, even if it holds the same contents.
func TestGuaranteedUpdateCachedNoopChecksPreconditions(t *testing.T) {
	ctx, store, _ := testSetup(t)
	key := "/pods/test-ns/foo"
	pod := &example.Pod{ObjectMeta: metav1.ObjectMeta{Name: "foo", Namespace: "test-ns", UID: "A"}}

	cached := &example.Pod{}
	if err := store.Create(ctx, key, pod.DeepCopy(), cached, 0); err != nil {
		t.Fatalf("Create failed: %v", err)
	}
	// Delete the object and create it again with the same contents: etcd now holds the same bytes
	// at a newer resource version.
	if err := store.Delete(ctx, key, &example.Pod{}, nil, storage.ValidateAllObjectFunc, nil, storage.DeleteOptions{}); err != nil {
		t.Fatalf("Delete failed: %v", err)
	}
	current := &example.Pod{}
	if err := store.Create(ctx, key, pod.DeepCopy(), current, 0); err != nil {
		t.Fatalf("Create failed: %v", err)
	}

	// An update that changes nothing, from the cached object, with a precondition on the cached
	// object's resource version.
	rv := cached.ResourceVersion
	out := &example.Pod{}
	err := store.GuaranteedUpdate(ctx, key, out, false, &storage.Preconditions{ResourceVersion: &rv},
		storage.SimpleUpdate(func(obj runtime.Object) (runtime.Object, error) { return obj, nil }),
		cached.DeepCopy())
	if !storage.IsInvalidObj(err) {
		t.Errorf("precondition ResourceVersion=%s on an object at ResourceVersion=%s: expected an InvalidObj error, got err=%v and the object at ResourceVersion=%q",
			rv, current.ResourceVersion, err, out.ResourceVersion)
	}
}
